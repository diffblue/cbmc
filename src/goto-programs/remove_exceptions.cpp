/*******************************************************************\

Module: Remove exception handling 

Author: Cristina David

Date:   December 2016

\*******************************************************************/

/// \file
/// Remove exception handling

#include "remove_exceptions.h"

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
    goto_functionst &goto_functions);

protected:
  symbol_tablet &symbol_table;
  std::map<irep_idt, std::set<irep_idt>> &exceptions_map;

  void add_exceptional_returns(
    const goto_functionst::function_mapt::iterator &);

  void instrument_exception_handler(
    const goto_functionst::function_mapt::iterator &,
    const goto_programt::instructionst::iterator &);

  void add_exception_dispatch_sequence(
    const goto_functionst::function_mapt::iterator &,
    const goto_programt::instructionst::iterator &instr_it,
    const stack_catcht &stack_catch,
    const std::vector<exprt> &locals);

  void instrument_throw(
    const goto_functionst::function_mapt::iterator &,
    const goto_programt::instructionst::iterator &,
    const stack_catcht &,
    const std::vector<exprt> &);

  void instrument_function_call(
    const goto_functionst::function_mapt::iterator &,
    const goto_programt::instructionst::iterator &,
    const stack_catcht &,
    const std::vector<exprt> &);

  void instrument_exceptions(
    const goto_functionst::function_mapt::iterator &);
};

/// adds exceptional return variables for every function that may escape
/// exceptions
void remove_exceptionst::add_exceptional_returns(
  const goto_functionst::function_mapt::iterator &func_it)
{
  const irep_idt &function_id=func_it->first;
  goto_programt &goto_program=func_it->second.body;

  INVARIANT(
    symbol_table.has_symbol(function_id),
    "functions should be recorded in the symbol table");
  const symbolt &function_symbol=symbol_table.lookup(function_id);

  // for now only add exceptional returns for Java
  if(function_symbol.mode!=ID_java)
    return;

  if(goto_program.empty())
    return;

  // some methods (e.g. the entry method) have already been added to
  // the symbol table; if you find it, initialise it
  if(symbol_table.has_symbol(id2string(function_id)+EXC_SUFFIX))
  {
    const symbolt &symbol=
      symbol_table.lookup(id2string(function_id)+EXC_SUFFIX);
    symbol_exprt lhs_expr_null=symbol.symbol_expr();
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
      symbol_tablet::symbolst::iterator s_it=
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
      new_symbol.type=typet(ID_pointer, empty_typet());
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
/// in-flight exception, hence marking it caught.
/// \param func_it: iterator pointing to the function containing this
///   landingpad instruction
/// \param instr_it [in, out]: iterator pointing to the landingpad instruction.
///   Will be overwritten.
void remove_exceptionst::instrument_exception_handler(
  const goto_functionst::function_mapt::iterator &func_it,
  const goto_programt::instructionst::iterator &instr_it)
{
  const irep_idt &function_id=func_it->first;
  goto_programt &goto_program=func_it->second.body;

  PRECONDITION(instr_it->type==CATCH);

  // retrieve the exception variable
  const auto &code_expr=to_code_expression(instr_it->code).expression();
  const exprt &thrown_exception_local=
    to_side_effect_expr_landingpad(code_expr).catch_expr();
  irep_idt thrown_exception_global=id2string(function_id)+EXC_SUFFIX;

  if(symbol_table.has_symbol(thrown_exception_global))
  {
    const symbol_exprt thrown_global_symbol=
      symbol_table.lookup(thrown_exception_global).symbol_expr();
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
/// if (exception instanceof ExnA) then goto handlera
/// else if (exception instanceof ExnB) then goto handlerb
/// else goto universal_handler or (dead locals; function exit)
/// \param function_id: function instr_it belongs to
/// \param instr_it: throw or call instruction that may be an
///   exception source
/// \param stack_catch: exception handlers currently registered
/// \param locals: local variables to kill on a function-exit edge
void remove_exceptionst::add_exception_dispatch_sequence(
  const goto_functionst::function_mapt::iterator &func_it,
  const goto_programt::instructionst::iterator &instr_it,
  const remove_exceptionst::stack_catcht &stack_catch,
  const std::vector<exprt> &locals)
{
  const irep_idt &function_id=func_it->first;
  goto_programt &goto_program=func_it->second.body;

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
        symbol_table.lookup(id2string(function_id)+EXC_SUFFIX);
  symbol_exprt exc_thrown=exc_symbol.symbol_expr();

  // add GOTOs implementing the dynamic dispatch of the
  // exception handlers
  for(std::size_t i=stack_catch.size(); i-->0;)
  {
    for(std::size_t j=stack_catch[i].size(); j-->0;)
    {
      goto_programt::targett new_state_pc=
        stack_catch[i][j].second;
      if(stack_catch[i][j].first==irep_idt())
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

/// instruments each throw with conditional GOTOS to the  corresponding
/// exception handlers
void remove_exceptionst::instrument_throw(
  const goto_functionst::function_mapt::iterator &func_it,
  const goto_programt::instructionst::iterator &instr_it,
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
    func_it, instr_it, stack_catch, locals);

  // find the symbol where the thrown exception should be stored:
  const symbolt &exc_symbol=
        symbol_table.lookup(id2string(func_it->first)+EXC_SUFFIX);
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
  const goto_functionst::function_mapt::iterator &func_it,
  const goto_programt::instructionst::iterator &instr_it,
  const stack_catcht &stack_catch,
  const std::vector<exprt> &locals)
{
  PRECONDITION(instr_it->type==FUNCTION_CALL);

  goto_programt &goto_program=func_it->second.body;
  const irep_idt &function_id=func_it->first;

  // save the address of the next instruction
  goto_programt::instructionst::iterator next_it=instr_it;
  next_it++;

  code_function_callt &function_call=to_code_function_call(instr_it->code);
  DATA_INVARIANT(
    function_call.function().id()==ID_symbol,
    "identified expected to be a symbol");
  const irep_idt &callee_id=
    to_symbol_expr(function_call.function()).get_identifier();

  const irep_idt &callee_inflight_exception=id2string(callee_id)+EXC_SUFFIX;
  const irep_idt &local_inflight_exception=id2string(function_id)+EXC_SUFFIX;

  if(symbol_table.has_symbol(callee_inflight_exception) &&
     symbol_table.has_symbol(local_inflight_exception))
  {
    add_exception_dispatch_sequence(
      func_it, instr_it, stack_catch, locals);

    const symbol_exprt callee_inflight_exception_expr=
      symbol_table.lookup(callee_inflight_exception).symbol_expr();
    const symbol_exprt local_inflight_exception_expr=
      symbol_table.lookup(local_inflight_exception).symbol_expr();

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
  const goto_functionst::function_mapt::iterator &func_it)
{
  stack_catcht stack_catch; // stack of try-catch blocks
  std::vector<std::vector<exprt>> stack_locals; // stack of local vars
  std::vector<exprt> locals;
  goto_programt &goto_program=func_it->second.body;

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
      // Is it an exception landing pad (start of a catch block)?
      if(instr_it->code.get_statement()==ID_expression &&
         instr_it->code.op0().id()==ID_side_effect &&
         to_side_effect_expr(instr_it->code.op0()).get_statement()==
         ID_exception_landingpad)
      {
        instrument_exception_handler(func_it, instr_it);
      }
      else if(instr_it->targets.empty()) // pop exception handler
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
      else // push exception handler
      {
        stack_locals.push_back(locals);
        locals.clear();

        remove_exceptionst::catch_handlerst exception;
        stack_catch.push_back(exception);
        remove_exceptionst::catch_handlerst &last_exception=
          stack_catch.back();

        // copy targets
        const irept::subt &exception_list=
          instr_it->code.find(ID_exception_list).get_sub();
        INVARIANT(
          exception_list.size()==instr_it->targets.size(),
          "`exception_list` should contain current instruction's targets");

        // Fill the map with the catch type and the target
        unsigned i=0;
        for(auto target : instr_it->targets)
        {
          last_exception.push_back(
            std::make_pair(exception_list[i].id(), target));
          i++;
        }
      }
      instr_it->make_skip();
    }
    else if(instr_it->type==THROW)
    {
      instrument_throw(func_it, instr_it, stack_catch, locals);
    }
    else if(instr_it->type==FUNCTION_CALL)
    {
      instrument_function_call(func_it, instr_it, stack_catch, locals);
    }
  }
}

void remove_exceptionst::operator()(goto_functionst &goto_functions)
{
  Forall_goto_functions(it, goto_functions)
    add_exceptional_returns(it);
  Forall_goto_functions(it, goto_functions)
    instrument_exceptions(it);
}

/// removes throws/CATCH-POP/CATCH-PUSH
void remove_exceptions(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  const namespacet ns(symbol_table);
  std::map<irep_idt, std::set<irep_idt>> exceptions_map;
  uncaught_exceptions(goto_functions, ns, exceptions_map);
  remove_exceptionst remove_exceptions(symbol_table, exceptions_map);
  remove_exceptions(goto_functions);
}

/// removes throws/CATCH-POP/CATCH-PUSH
void remove_exceptions(goto_modelt &goto_model)
{
  std::map<irep_idt, std::set<irep_idt>> exceptions_map;
  remove_exceptionst remove_exceptions(
    goto_model.symbol_table,
    exceptions_map);
  remove_exceptions(goto_model.goto_functions);
}
