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

#include <goto-programs/remove_skip.h>

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
/// java_instanceof, optionally lowered to a check on the @class_identifier
/// field, so a language frontend wanting to use this class must use
/// exceptions with a Java-compatible structure.
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
class remove_exceptionst
{
  typedef std::vector<std::pair<
    irep_idt, goto_programt::targett>> catch_handlerst;
  typedef std::vector<catch_handlerst> stack_catcht;

public:
  typedef std::function<bool(const irep_idt &)> function_may_throwt;

  explicit remove_exceptionst(
    symbol_table_baset &_symbol_table,
    const class_hierarchyt *class_hierarchy,
    function_may_throwt _function_may_throw,
    bool remove_added_instanceof,
    message_handlert &message_handler)
    : symbol_table(_symbol_table),
      class_hierarchy(class_hierarchy),
      function_may_throw(_function_may_throw),
      remove_added_instanceof(remove_added_instanceof),
      message_handler(message_handler)
  {
    if(remove_added_instanceof)
    {
      INVARIANT(
        class_hierarchy != nullptr,
        "remove_exceptions needs a class hierarchy to remove instanceof "
        "statements (either supply one, or don't use REMOVE_ADDED_INSTANCEOF)");
    }
  }

  void operator()(goto_functionst &goto_functions);
  void operator()(goto_programt &goto_program);

protected:
  symbol_table_baset &symbol_table;
  const class_hierarchyt *class_hierarchy;
  function_may_throwt function_may_throw;
  bool remove_added_instanceof;
  message_handlert &message_handler;

  symbol_exprt get_inflight_exception_global();

  bool function_or_callees_may_throw(const goto_programt &) const;

  void instrument_exception_handler(
    goto_programt &goto_program,
    const goto_programt::targett &,
    bool may_catch);

  goto_programt::targett find_universal_exception(
    const remove_exceptionst::stack_catcht &stack_catch,
    goto_programt &goto_program,
    std::size_t &universal_try,
    std::size_t &universal_catch);

  void add_exception_dispatch_sequence(
    goto_programt &goto_program,
    const goto_programt::targett &instr_it,
    const stack_catcht &stack_catch,
    const std::vector<exprt> &locals);

  bool instrument_throw(
    goto_programt &goto_program,
    const goto_programt::targett &,
    const stack_catcht &,
    const std::vector<exprt> &);

  bool instrument_function_call(
    goto_programt &goto_program,
    const goto_programt::targett &,
    const stack_catcht &,
    const std::vector<exprt> &);

  void instrument_exceptions(
    goto_programt &goto_program);
};

/// Create a global named java::\@inflight_exception that holds any exception
/// that has been thrown but not yet caught.
symbol_exprt remove_exceptionst::get_inflight_exception_global()
{
  const symbolt *existing_symbol =
    symbol_table.lookup(INFLIGHT_EXCEPTION_VARIABLE_NAME);
  INVARIANT(
    existing_symbol != nullptr,
    "Java frontend should have created @inflight_exception variable");
  return existing_symbol->symbol_expr();
}

/// Checks whether a function may ever experience an exception (whether or not
/// it catches), either by throwing one itself, or by calling a function that
/// exceptions escape from.
/// \param goto_program: program to check for throws and throwing calls
/// \return true if any throw or throwing call was found
bool remove_exceptionst::function_or_callees_may_throw(
  const goto_programt &goto_program) const
{
  forall_goto_program_instructions(instr_it, goto_program)
  {
    if(instr_it->is_throw())
    {
      return true;
    }

    if(instr_it->is_function_call())
    {
      const exprt &function_expr=
        to_code_function_call(instr_it->code).function();
      DATA_INVARIANT(
        function_expr.id()==ID_symbol,
        "identifier expected to be a symbol");
      const irep_idt &function_name=
        to_symbol_expr(function_expr).get_identifier();
      if(function_may_throw(function_name))
        return true;
    }
  }

  return false;
}

/// Translates an exception landing-pad into instructions that copy the
/// in-flight exception pointer to a nominated expression, then clear the
/// in-flight exception (i.e. null the pointer), hence marking it caught.
/// \param goto_program: body of the function containing this landingpad
///   instruction
/// \param instr_it: iterator pointing to the landingpad instruction.
///   Will be overwritten.
/// \param may_catch: if true, an exception may be caught here; otherwise
///   the catch site is unreachable. At present this will only be false if this
///   function is known never to throw, and never to call functions that throw.
void remove_exceptionst::instrument_exception_handler(
  goto_programt &goto_program,
  const goto_programt::targett &instr_it,
  bool may_catch)
{
  PRECONDITION(instr_it->type==CATCH);

  if(may_catch)
  {
    // retrieve the exception variable
    const exprt &thrown_exception_local=
      to_code_landingpad(instr_it->code).catch_expr();

    const symbol_exprt thrown_global_symbol=
      get_inflight_exception_global();
    // next we reset the exceptional return to NULL
    null_pointer_exprt null_voidptr((pointer_type(empty_typet())));

    // add the assignment @inflight_exception = NULL
    goto_programt::targett t_null=goto_program.insert_after(instr_it);
    t_null->make_assignment();
    t_null->source_location=instr_it->source_location;
    t_null->code=code_assignt(
      thrown_global_symbol,
      null_voidptr);
    t_null->function=instr_it->function;

    // add the assignment exc = @inflight_exception (before the null assignment)
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

/// Find the innermost universal exception handler for the current
/// program location which may throw (i.e. the first catch of type
/// any in the innermost try that contains such). We record this one
/// because no handler after it can possibly catch.
/// The context is contained in stack_catch which is a stack of all the tries
/// which contain the current program location in their bodies. Each of these
/// in turn contains a list of all possible catches for that try giving the
/// type of exception they catch and the location of the handler.
/// This function returns the indices of the try and the catch within that try
/// as well as the location of the handler.
/// The first loop is in forward order because the insertion reverses the order
/// we note  that try1{ try2 {} catch2c {} catch2d {}} catch1a() {} catch1b{}
/// must catch in the following order: 2c 2d 1a 1b hence the numerical index
/// is reversed whereas the letter ordering remains the same.
/// @param stack_catch exception table
/// @param goto_program program being evaluated
/// @param[out] universal_try returns the try block
///        corresponding to the desired exception handler
/// @param[out] universal_catch returns the catch block
///        corresponding to the exception desired exception handler
/// @return the desired exception handler
goto_programt::targett remove_exceptionst::find_universal_exception(
  const remove_exceptionst::stack_catcht &stack_catch,
  goto_programt &goto_program,
  std::size_t &universal_try,
  std::size_t &universal_catch)
{
  for(std::size_t i=stack_catch.size(); i>0;)
  {
    i--;
    for(std::size_t j=0; j<stack_catch[i].size(); ++j)
    {
      if(stack_catch[i][j].first.empty())
      {
        // Record the position of the default behaviour as any further catches
        // will not capture the throw
        universal_try=i;
        universal_catch=j;

        // Universal handler. Highest on the stack takes
        // precedence, so overwrite any we've already seen:
        return stack_catch[i][j].second;
      }
    }
  }
  // Unless we have a universal exception handler, jump to end of function
  return goto_program.get_end_function();
}

/// Emit the code:
/// if (exception instanceof ExnA) then goto handlerA
/// else if (exception instanceof ExnB) then goto handlerB
/// else goto universal_handler or (dead locals; function exit)
/// \param goto_program: body of the function to which instr_it belongs
/// \param instr_it: throw or call instruction that may be an
///   exception source
/// \param stack_catch: exception handlers currently registered
/// \param locals: local variables to kill on a function-exit edge
void remove_exceptionst::add_exception_dispatch_sequence(
  goto_programt &goto_program,
  const goto_programt::targett &instr_it,
  const remove_exceptionst::stack_catcht &stack_catch,
  const std::vector<exprt> &locals)
{
  // Jump to the universal handler or function end, as appropriate.
  // This will appear after the GOTO-based dynamic dispatch below
  goto_programt::targett default_dispatch=goto_program.insert_after(instr_it);

  // find the symbol corresponding to the caught exceptions
  symbol_exprt exc_thrown =
    get_inflight_exception_global();

  std::size_t default_try=0;
  std::size_t default_catch=(!stack_catch.empty()) ? stack_catch[0].size() : 0;

  goto_programt::targett default_target=
    find_universal_exception(stack_catch, goto_program,
                           default_try, default_catch);

  // add GOTOs implementing the dynamic dispatch of the
  // exception handlers.
  // The first loop is in forward order because the insertion reverses the order
  // we note  that try1{ try2 {} catch2c {} catch2d {}} catch1a() {} catch1b{}
  // must catch in the following order: 2c 2d 1a 1b hence the numerical index
  // is reversed whereas the letter ordering remains the same.
  for(std::size_t i=default_try; i<stack_catch.size(); i++)
  {
    for(std::size_t j=(i==default_try) ? default_catch : stack_catch[i].size();
      j>0;)
    {
      j--;
      goto_programt::targett new_state_pc=
        stack_catch[i][j].second;
      if(!stack_catch[i][j].first.empty())
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

        if(remove_added_instanceof)
        {
          remove_instanceof(
            t_exc,
            goto_program,
            symbol_table,
            *class_hierarchy,
            message_handler);
        }
      }
    }
  }

  default_dispatch->make_goto(default_target);
  default_dispatch->source_location=instr_it->source_location;
  default_dispatch->function=instr_it->function;

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
bool remove_exceptionst::instrument_throw(
  goto_programt &goto_program,
  const goto_programt::targett &instr_it,
  const remove_exceptionst::stack_catcht &stack_catch,
  const std::vector<exprt> &locals)
{
  PRECONDITION(instr_it->type==THROW);

  const exprt &exc_expr=
    uncaught_exceptions_domaint::get_exception_symbol(instr_it->code);

  add_exception_dispatch_sequence(
    goto_program, instr_it, stack_catch, locals);

  // find the symbol where the thrown exception should be stored:
  symbol_exprt exc_thrown =
    get_inflight_exception_global();

  // add the assignment with the appropriate cast
  code_assignt assignment(
    exc_thrown,
    typecast_exprt(exc_expr, exc_thrown.type()));
  // now turn the `throw' into `assignment'
  instr_it->type=ASSIGN;
  instr_it->code=assignment;

  return true;
}

/// instruments each function call that may escape exceptions with conditional
/// GOTOS to the corresponding exception handlers
bool remove_exceptionst::instrument_function_call(
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

  if(function_may_throw(callee_id))
  {
    equal_exprt no_exception_currently_in_flight(
      get_inflight_exception_global(),
      null_pointer_exprt(pointer_type(empty_typet())));

    if(symbol_table.lookup_ref(callee_id).type.get_bool(ID_C_must_not_throw))
    {
      // Function is annotated must-not-throw, but we can't prove that here.
      // Insert an ASSUME(@inflight_exception == null):
      goto_programt::targett assume_null = goto_program.insert_after(instr_it);
      assume_null->make_assumption(no_exception_currently_in_flight);
    }
    else
    {
      add_exception_dispatch_sequence(
        goto_program, instr_it, stack_catch, locals);

      // add a null check (so that instanceof can be applied)
      goto_programt::targett t_null=goto_program.insert_after(instr_it);
      t_null->make_goto(next_it);
      t_null->source_location=instr_it->source_location;
      t_null->function=instr_it->function;
      t_null->guard=no_exception_currently_in_flight;
    }

    return true;
  }

  return false;
}

/// instruments throws, function calls that may escape exceptions and exception
/// handlers. Additionally, it re-computes the live-range of local variables in
/// order to add DEAD instructions.
void remove_exceptionst::instrument_exceptions(
  goto_programt &goto_program)
{
  stack_catcht stack_catch; // stack of try-catch blocks
  std::vector<std::vector<exprt>> stack_locals; // stack of local vars
  std::vector<exprt> locals;

  if(goto_program.empty())
    return;

  bool program_or_callees_may_throw =
    function_or_callees_may_throw(goto_program);

  bool did_something = false;

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
        instrument_exception_handler(
          goto_program, instr_it, program_or_callees_may_throw);
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
      did_something = true;
    }
    else if(instr_it->type==THROW)
    {
      did_something |=
        instrument_throw(goto_program, instr_it, stack_catch, locals);
    }
    else if(instr_it->type==FUNCTION_CALL)
    {
      did_something |=
        instrument_function_call(goto_program, instr_it, stack_catch, locals);
    }
  }

  if(did_something)
    remove_skip(goto_program);
}

void remove_exceptionst::operator()(goto_functionst &goto_functions)
{
  Forall_goto_functions(it, goto_functions)
    instrument_exceptions(it->second.body);
}

void remove_exceptionst::operator()(goto_programt &goto_program)
{
  instrument_exceptions(goto_program);
}

/// removes throws/CATCH-POP/CATCH-PUSH
void remove_exceptions(
  symbol_table_baset &symbol_table,
  const class_hierarchyt *class_hierarchy,
  goto_functionst &goto_functions,
  message_handlert &message_handler,
  remove_exceptions_typest type)
{
  const namespacet ns(symbol_table);
  std::map<irep_idt, std::set<irep_idt>> exceptions_map;
  uncaught_exceptions(goto_functions, ns, exceptions_map);
  remove_exceptionst::function_may_throwt function_may_throw =
    [&exceptions_map](const irep_idt &id) {
      return !exceptions_map[id].empty();
    };
  remove_exceptionst remove_exceptions(
    symbol_table,
    class_hierarchy,
    function_may_throw,
    type == remove_exceptions_typest::REMOVE_ADDED_INSTANCEOF,
    message_handler);
  remove_exceptions(goto_functions);
}

/// removes throws/CATCH-POP/CATCH-PUSH from a single GOTO program, replacing
/// them with explicit exception propagation.
/// Note this is somewhat less accurate than the whole-goto-model version,
/// because we can't inspect other functions to determine whether they throw
/// or not, and therefore must assume they do and always introduce post-call
/// exception dispatch.
/// \param goto_program: program to remove exceptions from
/// \param symbol_table: global symbol table. The `@inflight_exception` global
///   may be added if not already present. It will not be initialised; that is
///   the caller's responsibility.
/// \param class_hierarchy: class hierarchy analysis of symbol_table.
///   Only needed if type == REMOVE_ADDED_INSTANCEOF; otherwise may be null.
/// \param message_handler: logging output
/// \param type: specifies whether instanceof operations generated by this pass
///   should be lowered to class-identifier comparisons (using
///   remove_instanceof).
void remove_exceptions(
  goto_programt &goto_program,
  symbol_table_baset &symbol_table,
  const class_hierarchyt *class_hierarchy,
  message_handlert &message_handler,
  remove_exceptions_typest type)
{
  remove_exceptionst::function_may_throwt any_function_may_throw =
    [](const irep_idt &) { return true; };

  remove_exceptionst remove_exceptions(
    symbol_table,
    class_hierarchy,
    any_function_may_throw,
    type == remove_exceptions_typest::REMOVE_ADDED_INSTANCEOF,
    message_handler);
  remove_exceptions(goto_program);
}

/// removes throws/CATCH-POP/CATCH-PUSH, replacing them with explicit exception
/// propagation.
/// \param goto_model: model to remove exceptions from. The
///   `@inflight_exception` global may be added to its symbol table if not
///   already present. It will not be initialised; that is the caller's
///   responsibility.
/// \param class_hierarchy: class hierarchy analysis of symbol_table.
///   Only needed if type == REMOVE_ADDED_INSTANCEOF; otherwise may be null.
/// \param message_handler: logging output
/// \param type: specifies whether instanceof operations generated by this pass
///   should be lowered to class-identifier comparisons (using
///   remove_instanceof).
void remove_exceptions(
  goto_modelt &goto_model,
  const class_hierarchyt *class_hierarchy,
  message_handlert &message_handler,
  remove_exceptions_typest type)
{
  remove_exceptions(
    goto_model.symbol_table,
    class_hierarchy,
    goto_model.goto_functions,
    message_handler,
    type);
}
