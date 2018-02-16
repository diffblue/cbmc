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
  /// Structure representing a try-block or the top-level function scope.
  /// Any scope may have local variables. A try-block may have one or more catch
  /// handlers and perhaps a finally block. The top-level function scope always
  /// has one handler, catching any exception and branching to end of function.
  struct try_scopet
  {
    typedef optionalt<goto_programt::targett> optional_instructiont;

    explicit try_scopet(
      goto_programt::targett block_end_instruction) :
      block_end_instruction(block_end_instruction)
    {
    }

    /// End instruction for the given scope. For a try-block this is the
    /// pop-try-block instruction; for the top-level function it is the end-of-
    /// function instruction.
    goto_programt::targett block_end_instruction;

    /// List of exception-type-id -> catch-handler-start mappings, indicating
    /// that if in a particular scope an exception with exception-type-id is
    /// thrown, it will be caught at catch-handler-start.
    std::vector<std::pair<irep_idt, goto_programt::targett>> catch_handlers;
  };

  /// Stack of try-block scopes. The bottom-most entry always represents the
  /// top-level function scope, outside any try block.
  typedef std::vector<try_scopet> try_scope_stackt;

  /// Map from <source-try-block, destination-catch-block> to the head of a
  /// sequence of instructions that kill the locals belonging to this
  /// and parent try-blocks, then branch to the given catch block.
  /// We share DEAD instructions as much as possible by branching to the exit
  /// sequence already existing for parent try blocks where they already exist.
  typedef
    std::map<std::pair<unsigned, unsigned>, goto_programt::targett>
    exit_sequence_mapt;

public:
  explicit remove_exceptionst(
    symbol_tablet &_symbol_table,
    std::map<irep_idt, std::set<irep_idt>> &_exceptions_map,
    bool remove_added_instanceof)
    : symbol_table(_symbol_table),
      exceptions_map(_exceptions_map),
      remove_added_instanceof(remove_added_instanceof)
  {
  }

  void operator()(goto_functionst &goto_functions);

protected:
  symbol_tablet &symbol_table;
  std::map<irep_idt, std::set<irep_idt>> &exceptions_map;
  bool remove_added_instanceof;

  std::unordered_map<
    goto_programt::targett, goto_programt::targett, const_target_hash>
  try_block_push_to_pop_map;

  std::unordered_map<
    goto_programt::targett, std::vector<exprt>, const_target_hash>
  scope_local_variables;

  void populate_try_block_maps(goto_programt &);

  symbol_exprt get_inflight_exception_global();

  bool function_or_callees_may_throw(const goto_programt &) const;

  void instrument_exception_handler(
    goto_programt &goto_program,
    const goto_programt::targett &,
    bool may_catch);

  goto_programt::targett find_universal_exception(
    const try_scope_stackt &,
    goto_programt &goto_program,
    std::size_t &universal_try,
    std::size_t &universal_catch);

  goto_programt::targett get_or_create_scope_exit_sequence(
    const try_scope_stackt &,
    std::size_t try_stack_index,
    std::size_t catch_stack_index,
    exit_sequence_mapt &,
    goto_programt::targett target_catch_block,
    goto_programt &goto_program);

  goto_programt::targett get_or_create_exit_sequence(
    const try_scope_stackt &try_scope_stack,
    std::size_t catch_stack_index,
    exit_sequence_mapt &exit_sequence_map,
    goto_programt::targett target_catch_block,
    goto_programt &goto_program)
  {
    return get_or_create_scope_exit_sequence(
      try_scope_stack,
      try_scope_stack.size() - 1,
      catch_stack_index,
      exit_sequence_map,
      target_catch_block,
      goto_program);
  }

  void add_exception_dispatch_sequence(
    goto_programt &goto_program,
    const goto_programt::targett &instr_it,
    const try_scope_stackt &,
    exit_sequence_mapt &);

  void instrument_throw(
    goto_programt &goto_program,
    const goto_programt::targett &,
    const try_scope_stackt &,
    exit_sequence_mapt &);

  void instrument_function_call(
    goto_programt &goto_program,
    const goto_programt::targett &,
    const try_scope_stackt &,
    exit_sequence_mapt &);

  void instrument_exceptions(
    goto_programt &goto_program);
};

/// Populate `try_block_push_to_pop_map` with a simple mapping from all
/// try-push instructions to the corresponding try-pop, and
/// scope_local_variables with all declarations made within a given try scope.
/// \param goto_program: program to search for instructions.
void remove_exceptionst::populate_try_block_maps(
  goto_programt &goto_program)
{
  try_block_push_to_pop_map.clear();

  std::vector<goto_programt::targett> try_block_stack;
  // The local variables stack begins with a top-level frame.
  std::vector<std::vector<exprt>> local_variables_stack(1);
  std::vector<unsigned> location_numbers;

  // Note this is a writable iterator because the values stored in the map will
  // later be used to insert instructions. This function does not itself alter
  // the GOTO program.
  Forall_goto_program_instructions(instr_it, goto_program)
  {
    if(instr_it->type == CATCH)
    {
      const irep_idt &statement = instr_it->code.get_statement();
      if(statement == ID_push_catch)
      {
        try_block_stack.push_back(instr_it);
        local_variables_stack.push_back({});
        location_numbers.push_back(instr_it->location_number);
      }
      else if(statement == ID_pop_catch)
      {
        INVARIANT(!try_block_stack.empty(), "try blocks should be well-nested");
        auto insert_result =
          try_block_push_to_pop_map.emplace(try_block_stack.back(), instr_it);
        INVARIANT(insert_result.second, "try block headers should be unique");
        auto insert_result2 =
          scope_local_variables.emplace(
            instr_it, std::move(local_variables_stack.back()));
        INVARIANT(
          insert_result2.second, "try block end instructions should be unique");
        try_block_stack.pop_back();
        local_variables_stack.pop_back();
        location_numbers.push_back(instr_it->location_number);
      }
    }
    else if(instr_it->type == DECL)
    {
      // Add local variable to the current scope
      code_declt decl=to_code_decl(instr_it->code);
      local_variables_stack.back().push_back(decl.symbol());
    }
  }

  // Record the local variables belonging to the top-level scope:
  INVARIANT(
    local_variables_stack.size() == 1,
    "after all try blocks have exited, only the top-level scope should remain");
  auto top_level_insert_result =
    scope_local_variables.emplace(
      goto_program.get_end_function(),
      std::move(local_variables_stack.back()));
  INVARIANT(
    top_level_insert_result.second,
    "end function instruction should not be in local variables map");

  // Check that the block start and end instructions all have unique location
  // numbers, so it is safe to use them as unique keys:
  std::sort(location_numbers.begin(), location_numbers.end());
  INVARIANT(
    std::unique(location_numbers.begin(), location_numbers.end()) ==
    location_numbers.end(),
    "try-block start and finish instructions should have unique "
    "location numbers");
}

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
      const exprt &exc =
        uncaught_exceptions_domaint::get_exception_symbol(instr_it->code);
      bool is_assertion_error =
        id2string(uncaught_exceptions_domaint::get_exception_type(exc.type())).
        find("java.lang.AssertionError")!=std::string::npos;
      if(!is_assertion_error)
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
      bool callee_may_throw = !exceptions_map[function_name].empty();
      if(callee_may_throw)
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
  const try_scope_stackt &try_scope_stack,
  goto_programt &goto_program,
  std::size_t &universal_try,
  std::size_t &universal_catch)
{
  for(std::size_t i=try_scope_stack.size(); i>0;)
  {
    i--;
    const try_scopet &try_scope = try_scope_stack.at(i);
    for(std::size_t j = 0; j < try_scope.catch_handlers.size(); ++j)
    {
      if(try_scope.catch_handlers[j].first.empty())
      {
        // Record the position of the default behaviour as any further catches
        // will not capture the throw
        universal_try=i;
        universal_catch=j;

        // Universal handler. Highest on the stack takes
        // precedence, so overwrite any we've already seen:
        return try_scope.catch_handlers[j].second;
      }
    }
  }
  // There must be at least one universal handler on the stack, the last/
  // fallback being the top-level scope, which should direct all exceptions to
  // end of function.
  UNREACHABLE;
}

/// Get or create a sequence of DEAD instructions leading from the
/// stack_index'th try scope to the given target catch block. This re-uses lower
/// scopes' exit sequences if they already exist, thus limiting the maximum
/// number of DEAD instructions according to the number of distinct source /
/// destination pairs.
/// \param try_scope_stack: try scope stack
/// \param try_stack_index: index in the try scope stack to create an
///   exit sequence for
/// \param catch_stack_index: try scope index where the target catch handler
///   occurs, and thus the last scope to generate exit sequences for.
/// \param exit_sequence_map: map from (throwing-scope, target-instruction) to
///   an existing exit sequence, if any. An existing sequence will be used if
///   present, or a new one will be added otherwise.
/// \param target_catch_block: ultimate target of this exit sequence.
/// \param goto_program: program containing target_catch_block.
goto_programt::targett remove_exceptionst::get_or_create_scope_exit_sequence(
  const try_scope_stackt &try_scope_stack,
  std::size_t try_stack_index,
  std::size_t catch_stack_index,
  exit_sequence_mapt &exit_sequence_map,
  goto_programt::targett target_catch_block,
  goto_programt &goto_program)
{
  // Must exit down the lexical scope hierarchy:
  PRECONDITION(try_stack_index >= catch_stack_index);

  const try_scopet &try_scope = try_scope_stack.at(try_stack_index);

  // Use an existing exit sequence if possible:
  exit_sequence_mapt::key_type sequence_map_key
  {
    try_scope.block_end_instruction->location_number,
    target_catch_block->location_number
  };

  auto insertit = exit_sequence_map.insert({sequence_map_key, {}});
  if(!insertit.second)
    return insertit.first->second;

  // If necessary, get an exit sequence for the next try-block down, and branch
  // to that once we're done exiting this scope. Otherwise, simply branch to
  // the target catch block or function exit:
  goto_programt::targett next_target;
  if(try_stack_index != catch_stack_index)
  {
    next_target =
      get_or_create_scope_exit_sequence(
        try_scope_stack,
        try_stack_index - 1,
        catch_stack_index,
        exit_sequence_map,
        target_catch_block,
        goto_program);
  }
  else
  {
    next_target = target_catch_block;
  }

  const std::vector<exprt> &this_scope_locals =
    scope_local_variables.at(try_scope.block_end_instruction);

  goto_programt::targett result;
  if(this_scope_locals.empty())
  {
    // Nothing to clean up at this scope -- simply jump to the next target,
    // whether it's the next scope out or the ultimate destination:
    result = next_target;
  }
  else
  {
    // Put the new exit sequence directly before the end of this scope, which
    // means either the end the function, or the end of a try block.
    goto_programt::targett insert_point = try_scope.block_end_instruction;

    // Insert a GOTO so that existing code landing at the insert point branches
    // around our new exit sequence:
    if(!std::prev(insert_point)->is_goto())
    {
      goto_programt::targett goto_around =
        goto_program.insert_before(insert_point);
      goto_around->make_goto(insert_point);
      goto_around->source_location = insert_point->source_location;
      goto_around->function = insert_point->function;
    }

    // Add dead instructions for locals declared at this scope:
    bool first_dead = true;
    INVARIANT(
      !this_scope_locals.empty(),
      "should have at least one dead instruction to generate");
    for(const auto &local : this_scope_locals)
    {
      goto_programt::targett t_dead = goto_program.insert_before(insert_point);
      t_dead->make_dead();
      t_dead->code = code_deadt(local);
      t_dead->source_location = insert_point->source_location;
      t_dead->function = insert_point->function;
      if(first_dead)
      {
        // This first DEAD instruction is the start of the exit sequence:
        result = t_dead;
        first_dead = false;
      }
    }

    // Finally, branch to the next try-block exit sequence or the target:
    goto_programt::targett t_goto = goto_program.insert_before(insert_point);
    t_goto->make_goto(next_target);
    t_goto->source_location = insert_point->source_location;
    t_goto->function = insert_point->function;
  }

  // Save this result for future use:
  insertit.first->second = result;

  return result;
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
  const try_scope_stackt &try_scope_stack,
  exit_sequence_mapt &exit_sequence_map)
{
  // Jump to the universal handler or function end, as appropriate.
  // This will appear after the GOTO-based dynamic dispatch below
  goto_programt::targett default_dispatch=goto_program.insert_after(instr_it);
  default_dispatch->make_goto();
  default_dispatch->source_location=instr_it->source_location;
  default_dispatch->function=instr_it->function;

  // find the symbol corresponding to the caught exceptions
  symbol_exprt exc_thrown =
    get_inflight_exception_global();

  std::size_t default_try = 0;
  std::size_t default_catch = try_scope_stack.front().catch_handlers.size();

  goto_programt::targett default_target=
    find_universal_exception(
      try_scope_stack, goto_program, default_try, default_catch);

  // add GOTOs implementing the dynamic dispatch of the
  // exception handlers.
  // The first loop is in forward order because the insertion reverses the order
  // we note  that try1{ try2 {} catch2c {} catch2d {}} catch1a() {} catch1b{}
  // must catch in the following order: 2c 2d 1a 1b hence the numerical index
  // is reversed whereas the letter ordering remains the same.
  for(std::size_t i = default_try; i < try_scope_stack.size(); i++)
  {
    const auto &this_scope_handlers = try_scope_stack[i].catch_handlers;
    for(std::size_t j =
          (i == default_try) ? default_catch : this_scope_handlers.size();
        j > 0;)
    {
      j--;
      if(!this_scope_handlers[j].first.empty())
      {
        // Normal exception handler, make an instanceof check.
        // Make DEAD instructions leading from this try-block to the target
        // catch:
        goto_programt::targett new_state_pc =
          get_or_create_exit_sequence(
            try_scope_stack,
            i,
            exit_sequence_map,
            this_scope_handlers[j].second,
            goto_program);

        goto_programt::targett t_exc=goto_program.insert_after(instr_it);
        t_exc->make_goto(new_state_pc);
        t_exc->source_location=instr_it->source_location;
        t_exc->function=instr_it->function;

        // use instanceof to check that this is the correct handler
        symbol_typet type(this_scope_handlers[j].first);
        type_exprt expr(type);

        binary_predicate_exprt check(exc_thrown, ID_java_instanceof, expr);
        t_exc->guard=check;

        if(remove_added_instanceof)
          remove_instanceof(t_exc, goto_program, symbol_table);
      }
    }
  }

  default_dispatch->set_target(
    get_or_create_exit_sequence(
      try_scope_stack,
      default_try,
      exit_sequence_map,
      default_target,
      goto_program));
}

/// instruments each throw with conditional GOTOS to the corresponding
/// exception handlers
void remove_exceptionst::instrument_throw(
  goto_programt &goto_program,
  const goto_programt::targett &instr_it,
  const try_scope_stackt &try_scope_stack,
  exit_sequence_mapt &exit_sequence_map)
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
    goto_program, instr_it, try_scope_stack, exit_sequence_map);

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
}

/// instruments each function call that may escape exceptions with conditional
/// GOTOS to the corresponding exception handlers
void remove_exceptionst::instrument_function_call(
  goto_programt &goto_program,
  const goto_programt::targett &instr_it,
  const try_scope_stackt &try_scope_stack,
  exit_sequence_mapt &exit_sequence_map)
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

  bool callee_may_throw = !exceptions_map[callee_id].empty();

  if(callee_may_throw)
  {
    add_exception_dispatch_sequence(
      goto_program, instr_it, try_scope_stack, exit_sequence_map);

    // add a null check (so that instanceof can be applied)
    equal_exprt eq_null(
      get_inflight_exception_global(),
      null_pointer_exprt(pointer_type(empty_typet())));

    goto_programt::targett t_null=goto_program.insert_after(instr_it);
    t_null->make_goto(next_it);
    t_null->source_location=instr_it->source_location;
    t_null->function=instr_it->function;
    t_null->guard=eq_null;
  }
}

/// instruments throws, function calls that may escape exceptions and exception
/// handlers. Additionally, it re-computes the live-range of local variables in
/// order to add DEAD instructions.
void remove_exceptionst::instrument_exceptions(
  goto_programt &goto_program)
{
  if(goto_program.empty())
    return;

  // Make a quick pre-pass, establishing the correspondence between push- and
  // pop-try-block operations and local variables. This also ensures the
  // instructions concerned have unique numbers, so we can use them as map keys.
  populate_try_block_maps(goto_program);

  // Initialise top-level scope, representing the scope outside any try block.
  try_scope_stackt try_scope_stack;
  try_scope_stack.emplace_back(goto_program.get_end_function());
  try_scopet &top_scope = try_scope_stack.back();
  // Add a single exception handler, catching all exceptions and branching to
  // the end of the function:
  top_scope.catch_handlers.emplace_back(
    irep_idt(), goto_program.get_end_function());

  // This will map {try-block, destination-catch-block} pairs onto exit
  // sequences (DEAD instructions killing local variables) leading from that
  // try-block to the catch block. They are created on demand, so initially
  // this is empty.
  exit_sequence_mapt exit_sequences;

  bool program_or_callees_may_throw =
    function_or_callees_may_throw(goto_program);

  Forall_goto_program_instructions(instr_it, goto_program)
  {
    // Is it a handler push/pop or catch landing-pad?
    if(instr_it->type==CATCH)
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
        INVARIANT(
          try_scope_stack.size() >= 2,
          "try block push and pop instructions should be well-nested");
        try_scope_stack.pop_back();
      }
      // Is it a catch handler push?
      else if(statement==ID_push_catch)
      {
        // Add a new try-scope along with its exception handlers:
        try_scope_stack.emplace_back(try_block_push_to_pop_map.at(instr_it));
        try_scopet &new_scope = try_scope_stack.back();

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
          new_scope.catch_handlers.emplace_back(
            exception_list[i].get_tag(), target);
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
        goto_program, instr_it, try_scope_stack, exit_sequences);
    }
    else if(instr_it->type==FUNCTION_CALL)
    {
      instrument_function_call(
        goto_program, instr_it, try_scope_stack, exit_sequences);
    }
  }
}

void remove_exceptionst::operator()(goto_functionst &goto_functions)
{
  Forall_goto_functions(it, goto_functions)
    instrument_exceptions(it->second.body);
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
  remove_exceptionst remove_exceptions(
    symbol_table,
    exceptions_map,
    type == remove_exceptions_typest::REMOVE_ADDED_INSTANCEOF);
  remove_exceptions(goto_functions);
}

/// removes throws/CATCH-POP/CATCH-PUSH
void remove_exceptions(goto_modelt &goto_model, remove_exceptions_typest type)
{
  remove_exceptions(goto_model.symbol_table, goto_model.goto_functions, type);
}
