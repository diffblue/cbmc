/*******************************************************************\

Module: Remove exception handling

Author: Cristina David

Date:   December 2016

\*******************************************************************/

/// \file
/// Remove exception handling

#include "remove_exceptions.h"
#include "remove_instanceof.h"

#ifdef DEBUG
#include <iostream>
#endif

#include <stack>
#include <algorithm>

#include <util/c_types.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

#include <analyses/uncaught_exceptions_analysis.h>

/// Lowers high-level exception descriptions into low-level operations suitable
/// for symex and other analyses that don't understand the THROW or CATCH GOTO
/// instructions.
///
/// The instructions affected by the lowering are:
///
/// THROW, whose operand must be a code_expressiont wrapping a
/// side_effect_expr_throwt. This starts propagating an exception, aborting
/// functions until a suitable catch point is found.
///
/// CATCH with a code_push_catcht operand, which commences a region in which
/// exceptions should be caught, commonly a try block.
/// It specifies one or more exception tags to handle
/// (in instruction->code.exception_list()) and a corresponding GOTO program
/// target for each (in instruction->targets).
/// Thrown instructions are currently always matched to tags using
/// java_instanceof, so a language frontend wanting to use this class
/// must use exceptions with a Java-compatible structure.
///
/// CATCH with a code_pop_catcht operand terminates a try-block begun by
/// a code_push_catcht. At present the try block consists of the instructions
/// between the push and the pop *in program order*, not according to dynamic
/// control flow, so goto_convert_exceptions must ensure that control-flow
/// within the try block does not leave this range.
///
/// CATCH with a code_landingpadt operand marks a point where exceptional
/// control flow terminates and normal control flow resumes, typically the top
/// of a catch or finally block, and the target of a code_push_catcht
/// describing the correponding try block. It gives an lvalue expression that
/// should be assigned the caught exception, typically a local variable.
///
/// FUNCTION_CALL instructions are also affected: if the callee may abort
/// due to an escaping instruction, a dispatch sequence is inserted to check
/// whether the callee aborted and propagate the exception further if so.
///
/// Exception propagation is implemented using a global variable per function
/// (named function_name#exception_value) that carries a reference to an
/// in-flight exception, or is null during normal control flow.
/// THROW assigns it a reference to the thrown instance; CALL instructions
/// copy between the exception_value for the callee and caller, catch_push
/// and catch_pop instructions indicate how they should be checked to dispatch
/// the right exception type to the right catch block, and landingpad
/// instructions copy back to an ordinary local variable (or other expression)
/// and set \#exception_value back to null, indicating the exception has been
/// caught and normal control flow resumed.
///
/// Note that remove_exceptions introduces java_instanceof comparisons at
/// present, so a remove_instanceof may be necessary after it completes.
class remove_exceptionst
{
  typedef std::vector<std::pair<
    irep_idt, goto_programt::targett>> catch_handlerst;
  typedef std::vector<catch_handlerst> stack_catcht;

public:
  explicit remove_exceptionst(
    symbol_tablet &_symbol_table,
    std::map<irep_idt, std::set<irep_idt>> &_exceptions_map):
    symbol_table(_symbol_table),
    exceptions_map(_exceptions_map)
  {
  }

  void operator()(
    goto_functionst &goto_functions,
    remove_exceptions_typest type);

protected:
  symbol_tablet &symbol_table;
  std::map<irep_idt, std::set<irep_idt>> &exceptions_map;

  void add_exceptional_returns(
    const irep_idt &function_id,
    goto_programt &goto_program);

  void instrument_exception_handler(
    const irep_idt &function_id,
    goto_programt &goto_program,
    const goto_programt::targett &);

  void add_exception_dispatch_sequence(
    const irep_idt &function_id,
    goto_programt &goto_program,
    const goto_programt::targett &instr_it,
    const stack_catcht &stack_catch,
    const std::vector<exprt> &locals);

  void instrument_throw(
    const irep_idt &function_id,
    goto_programt &goto_program,
    const goto_programt::targett &,
    const stack_catcht &,
    const std::vector<exprt> &);

  void instrument_function_call(
    const irep_idt &function_id,
    goto_programt &goto_program,
    const goto_programt::targett &,
    const stack_catcht &,
    const std::vector<exprt> &);

  void instrument_exceptions(
    const irep_idt &function_id,
    goto_functionst::goto_functiont &function,
    remove_exceptions_typest type);
};

/// adds exceptional return variables for every function that may escape
/// exceptions
void remove_exceptionst::add_exceptional_returns(
  const irep_idt &function_id,
  goto_programt &goto_program)
{

  auto maybe_symbol=symbol_table.lookup(function_id);
  INVARIANT(maybe_symbol, "functions should be recorded in the symbol table");
  const symbolt &function_symbol=*maybe_symbol;

  // for now only add exceptional returns for Java
  if(function_symbol.mode!=ID_java)
    return;

  if(goto_program.empty())
    return;

  // some methods (e.g. the entry method) have already been added to
  // the symbol table; if you find it, initialise it
  maybe_symbol=symbol_table.lookup(id2string(function_id)+EXC_SUFFIX);
  if(maybe_symbol)
  {
    const symbolt &symbol=*maybe_symbol;
    symbol_exprt lhs_expr_null=symbol.symbol_expr();
    null_pointer_exprt rhs_expr_null((pointer_type(empty_typet())));
    goto_programt::targett t_null=
      goto_program.insert_before(goto_program.instructions.begin());
    t_null->make_assignment();
    t_null->source_location=
      goto_program.instructions.begin()->source_location;
    t_null->code=code_assignt(
      lhs_expr_null,
      rhs_expr_null);
    t_null->function=function_id;
    return;
  }

  // We generate an exceptional return value for any function that
  // contains a throw or a function call that may escape exceptions.
  forall_goto_program_instructions(instr_it, goto_program)
  {
    bool has_uncaught_exceptions=false;
    if(instr_it->is_function_call())
    {
      const exprt &function_expr=
        to_code_function_call(instr_it->code).function();
      DATA_INVARIANT(
        function_expr.id()==ID_symbol,
        "identifier expected to be a symbol");
      const irep_idt &function_name=
        to_symbol_expr(function_expr).get_identifier();
      has_uncaught_exceptions=!exceptions_map[function_name].empty();
    }

    bool assertion_error=false;
    if(instr_it->is_throw())
    {
      const exprt &exc =
        uncaught_exceptions_domaint::get_exception_symbol(instr_it->code);
      assertion_error =
        id2string(uncaught_exceptions_domaint::get_exception_type(exc.type())).
        find("java.lang.AssertionError")!=std::string::npos;
    }

    // if we find a throw different from AssertionError or a function call
    // that may escape exceptions, then we add an exceptional return
    // variable
    if((instr_it->is_throw() && !assertion_error)
       || has_uncaught_exceptions)
    {
      // look up the function symbol
      symbol_tablet::symbolst::const_iterator s_it=
        symbol_table.symbols.find(function_id);

      INVARIANT(
        s_it!=symbol_table.symbols.end(),
        "functions should be recorded in the symbol table");

      auxiliary_symbolt new_symbol;
      new_symbol.is_static_lifetime=true;
      new_symbol.module=function_symbol.module;
      new_symbol.base_name=id2string(function_symbol.base_name)+EXC_SUFFIX;
      new_symbol.name=id2string(function_symbol.name)+EXC_SUFFIX;
      new_symbol.mode=function_symbol.mode;
      new_symbol.type=pointer_type(empty_typet());
      symbol_table.add(new_symbol);

      // initialize the exceptional return with NULL
      symbol_exprt lhs_expr_null=new_symbol.symbol_expr();
      null_pointer_exprt rhs_expr_null(pointer_type(empty_typet()));
      goto_programt::targett t_null=
        goto_program.insert_before(goto_program.instructions.begin());
      t_null->make_assignment();
      t_null->source_location=
        goto_program.instructions.begin()->source_location;
      t_null->code=code_assignt(
        lhs_expr_null,
        rhs_expr_null);
      t_null->function=function_id;

      break;
    }
  }
}

/// Translates an exception landing-pad into instructions that copy the
/// in-flight exception pointer to a nominated expression, then clear the
/// in-flight exception (i.e. null the pointer), hence marking it caught.
/// \param function_id: name of the function containing this landingpad
///   instruction
/// \param goto_program: body of the function containing this landingpad
///   instruction
/// \param instr_it: iterator pointing to the landingpad instruction.
///   Will be overwritten.
void remove_exceptionst::instrument_exception_handler(
  const irep_idt &function_id,
  goto_programt &goto_program,
  const goto_programt::targett &instr_it)
{
  PRECONDITION(instr_it->type==CATCH);

  // retrieve the exception variable
  const exprt &thrown_exception_local=
    to_code_landingpad(instr_it->code).catch_expr();
  irep_idt thrown_exception_global=id2string(function_id)+EXC_SUFFIX;

  if(const auto maybe_symbol=symbol_table.lookup(thrown_exception_global))
  {
    const symbol_exprt thrown_global_symbol=maybe_symbol->symbol_expr();
    // next we reset the exceptional return to NULL
    null_pointer_exprt null_voidptr((pointer_type(empty_typet())));

    // add the assignment
    goto_programt::targett t_null=goto_program.insert_after(instr_it);
    t_null->make_assignment();
    t_null->source_location=instr_it->source_location;
    t_null->code=code_assignt(
      thrown_global_symbol,
      null_voidptr);
    t_null->function=instr_it->function;

    // add the assignment exc=f#exception_value (before the null assignment)
    goto_programt::targett t_exc=goto_program.insert_after(instr_it);
    t_exc->make_assignment();
    t_exc->source_location=instr_it->source_location;
    t_exc->code=code_assignt(
      thrown_exception_local,
      typecast_exprt(thrown_global_symbol, thrown_exception_local.type()));
    t_exc->function=instr_it->function;
  }
  instr_it->make_skip();
}

/// Emit the code:
/// if (exception instanceof ExnA) then goto handlerA
/// else if (exception instanceof ExnB) then goto handlerB
/// else goto universal_handler or (dead locals; function exit)
/// \param function_id: name of the function to which instr_it belongs
/// \param goto_program: body of the function to which instr_it belongs
/// \param instr_it: throw or call instruction that may be an
///   exception source
/// \param stack_catch: exception handlers currently registered
/// \param locals: local variables to kill on a function-exit edge
void remove_exceptionst::add_exception_dispatch_sequence(
  const irep_idt &function_id,
  goto_programt &goto_program,
  const goto_programt::targett &instr_it,
  const remove_exceptionst::stack_catcht &stack_catch,
  const std::vector<exprt> &locals)
{
  // Unless we have a universal exception handler, jump to end of function
  // if not caught:
  goto_programt::targett default_target=goto_program.get_end_function();

  // Jump to the universal handler or function end, as appropriate.
  // This will appear after the GOTO-based dynamic dispatch below
  goto_programt::targett default_dispatch=goto_program.insert_after(instr_it);
  default_dispatch->make_goto();
  default_dispatch->source_location=instr_it->source_location;
  default_dispatch->function=instr_it->function;

  // find the symbol corresponding to the caught exceptions
  const symbolt &exc_symbol=
    symbol_table.lookup_ref(id2string(function_id)+EXC_SUFFIX);
  symbol_exprt exc_thrown=exc_symbol.symbol_expr();

  // add GOTOs implementing the dynamic dispatch of the
  // exception handlers
  for(std::size_t i=stack_catch.size(); i-->0;)
  {
    for(std::size_t j=stack_catch[i].size(); j-->0;)
    {
      goto_programt::targett new_state_pc=
        stack_catch[i][j].second;
      if(stack_catch[i][j].first.empty())
      {
        // Universal handler. Highest on the stack takes
        // precedence, so overwrite any we've already seen:
        default_target=new_state_pc;
      }
      else
      {
        // Normal exception handler, make an instanceof check.
        goto_programt::targett t_exc=goto_program.insert_after(instr_it);
        t_exc->make_goto(new_state_pc);
        t_exc->source_location=instr_it->source_location;
        t_exc->function=instr_it->function;

        // use instanceof to check that this is the correct handler
        symbol_typet type(stack_catch[i][j].first);
        type_exprt expr(type);

        binary_predicate_exprt check(exc_thrown, ID_java_instanceof, expr);
        t_exc->guard=check;
      }
    }
  }

  default_dispatch->set_target(default_target);

  // add dead instructions
  for(const auto &local : locals)
  {
    goto_programt::targett t_dead=goto_program.insert_after(instr_it);
    t_dead->make_dead();
    t_dead->code=code_deadt(local);
    t_dead->source_location=instr_it->source_location;
    t_dead->function=instr_it->function;
  }
}

/// instruments each throw with conditional GOTOS to the corresponding
/// exception handlers
void remove_exceptionst::instrument_throw(
  const irep_idt &function_id,
  goto_programt &goto_program,
  const goto_programt::targett &instr_it,
  const remove_exceptionst::stack_catcht &stack_catch,
  const std::vector<exprt> &locals)
{
  PRECONDITION(instr_it->type==THROW);

  const exprt &exc_expr=
    uncaught_exceptions_domaint::get_exception_symbol(instr_it->code);
  bool assertion_error=id2string(
    uncaught_exceptions_domaint::get_exception_type(exc_expr.type())).
    find("java.lang.AssertionError")!=std::string::npos;

  // we don't count AssertionError (we couldn't catch it anyway
  // and this may reduce the instrumentation considerably if the programmer
  // used assertions)
  if(assertion_error)
    return;

  add_exception_dispatch_sequence(
    function_id, goto_program, instr_it, stack_catch, locals);

  // find the symbol where the thrown exception should be stored:
  const symbolt &exc_symbol=
    symbol_table.lookup_ref(id2string(function_id)+EXC_SUFFIX);
  symbol_exprt exc_thrown=exc_symbol.symbol_expr();

  // add the assignment with the appropriate cast
  code_assignt assignment(typecast_exprt(exc_thrown, exc_expr.type()),
                          exc_expr);
  // now turn the `throw' into `assignment'
  instr_it->type=ASSIGN;
  instr_it->code=assignment;
}

/// instruments each function call that may escape exceptions with conditional
/// GOTOS to the corresponding exception handlers
void remove_exceptionst::instrument_function_call(
  const irep_idt &function_id,
  goto_programt &goto_program,
  const goto_programt::targett &instr_it,
  const stack_catcht &stack_catch,
  const std::vector<exprt> &locals)
{
  PRECONDITION(instr_it->type==FUNCTION_CALL);

  // save the address of the next instruction
  goto_programt::targett next_it=instr_it;
  next_it++;

  code_function_callt &function_call=to_code_function_call(instr_it->code);
  DATA_INVARIANT(
    function_call.function().id()==ID_symbol,
    "identified expected to be a symbol");
  const irep_idt &callee_id=
    to_symbol_expr(function_call.function()).get_identifier();

  const auto callee_inflight_exception=
    symbol_table.lookup(id2string(callee_id)+EXC_SUFFIX);
  const auto local_inflight_exception=
    symbol_table.lookup(id2string(function_id)+EXC_SUFFIX);

  if(callee_inflight_exception && local_inflight_exception)
  {
    add_exception_dispatch_sequence(
      function_id, goto_program, instr_it, stack_catch, locals);

    const symbol_exprt callee_inflight_exception_expr=
      callee_inflight_exception->symbol_expr();
    const symbol_exprt local_inflight_exception_expr=
      local_inflight_exception->symbol_expr();

    // add a null check (so that instanceof can be applied)
    equal_exprt eq_null(
      local_inflight_exception_expr,
      null_pointer_exprt(pointer_type(empty_typet())));
    goto_programt::targett t_null=goto_program.insert_after(instr_it);
    t_null->make_goto(next_it);
    t_null->source_location=instr_it->source_location;
    t_null->function=instr_it->function;
    t_null->guard=eq_null;

    // after each function call g() in function f
    // adds f#exception_value=g#exception_value;
    goto_programt::targett t=goto_program.insert_after(instr_it);
    t->make_assignment();
    t->source_location=instr_it->source_location;
    t->code=code_assignt(
      local_inflight_exception_expr,
      callee_inflight_exception_expr);
    t->function=instr_it->function;
  }
}

/// instruments throws, function calls that may escape exceptions and exception
/// handlers. Additionally, it re-computes the live-range of local variables in
/// order to add DEAD instructions.
void remove_exceptionst::instrument_exceptions(
  const irep_idt &function_id,
  goto_functionst::goto_functiont &function,
  remove_exceptions_typest type)
{
  stack_catcht stack_catch; // stack of try-catch blocks
  std::vector<std::vector<exprt>> stack_locals; // stack of local vars
  std::vector<exprt> locals;
  goto_programt &goto_program=function.body;

  if(goto_program.empty())
    return;
  Forall_goto_program_instructions(instr_it, goto_program)
  {
    if(instr_it->is_decl())
    {
      code_declt decl=to_code_decl(instr_it->code);
      locals.push_back(decl.symbol());
    }
    // Is it a handler push/pop or catch landing-pad?
    else if(instr_it->type==CATCH)
    {
      const irep_idt &statement=instr_it->code.get_statement();
      // Is it an exception landing pad (start of a catch block)?
      if(statement==ID_exception_landingpad)
      {
        instrument_exception_handler(function_id, goto_program, instr_it);
      }
      // Is it a catch handler pop?
      else if(statement==ID_pop_catch)
      {
        // pop the local vars stack
        if(!stack_locals.empty())
        {
          locals=stack_locals.back();
          stack_locals.pop_back();
        }
        // pop from the stack if possible
        if(!stack_catch.empty())
        {
          stack_catch.pop_back();
        }
        else
        {
#ifdef DEBUG
          std::cout << "Remove exceptions: empty stack\n";
#endif
        }
      }
      // Is it a catch handler push?
      else if(statement==ID_push_catch)
      {
        stack_locals.push_back(locals);
        locals.clear();

        remove_exceptionst::catch_handlerst exception;
        stack_catch.push_back(exception);
        remove_exceptionst::catch_handlerst &last_exception=
          stack_catch.back();

        // copy targets
        const code_push_catcht::exception_listt &exception_list=
          to_code_push_catch(instr_it->code).exception_list();

        // The target list can be empty if `finish_catch_push_targets` found that
        // the targets were unreachable (in which case no exception can truly
        // be thrown at runtime)
        INVARIANT(
          instr_it->targets.empty() ||
          exception_list.size()==instr_it->targets.size(),
          "`exception_list` should contain current instruction's targets");

        // Fill the map with the catch type and the target
        unsigned i=0;
        for(auto target : instr_it->targets)
        {
          last_exception.push_back(
            std::make_pair(exception_list[i].get_tag(), target));
          i++;
        }
      }
      else
      {
        INVARIANT(
          false,
          "CATCH opcode should be one of push-catch, pop-catch, landingpad");
      }
      instr_it->make_skip();
    }
    else if(instr_it->type==THROW)
    {
      instrument_throw(
        function_id, goto_program, instr_it, stack_catch, locals);
    }
    else if(instr_it->type==FUNCTION_CALL)
    {
      instrument_function_call(
        function_id, goto_program, instr_it, stack_catch, locals);
    }
  }
  if(type==remove_exceptions_typest::REMOVE_ADDED_INSTANCEOF)
    INVARIANT(
      false,
      "Can't currently only remove added instanceof, use "
        "also_remove_instanceof");
  if(type==remove_exceptions_typest::ALSO_REMOVE_INSTANCEOF)
    remove_instanceof(function, symbol_table);
}

void remove_exceptionst::operator()(
  goto_functionst &goto_functions,
  remove_exceptions_typest type)
{
  Forall_goto_functions(it, goto_functions)
    add_exceptional_returns(it->first, it->second.body);
  Forall_goto_functions(it, goto_functions)
    instrument_exceptions(it->first, it->second, type);
}

/// removes throws/CATCH-POP/CATCH-PUSH
void remove_exceptions(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  remove_exceptions_typest type)
{
  const namespacet ns(symbol_table);
  std::map<irep_idt, std::set<irep_idt>> exceptions_map;
  uncaught_exceptions(goto_functions, ns, exceptions_map);
  remove_exceptionst remove_exceptions(symbol_table, exceptions_map);
  remove_exceptions(goto_functions, type);
}

/// removes throws/CATCH-POP/CATCH-PUSH
void remove_exceptions(goto_modelt &goto_model, remove_exceptions_typest type)
{
  remove_exceptions(
    goto_model.symbol_table,
    goto_model.goto_functions,
    type);
}
