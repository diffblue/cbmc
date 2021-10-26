/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <memory>

#include <pointer-analysis/value_set_dereference.h>

#include <util/exception_utils.h>
#include <util/expr_iterator.h>
#include <util/expr_util.h>
#include <util/format.h>
#include <util/format_expr.h>
#include <util/invariant.h>
#include <util/make_unique.h>
#include <util/mathematical_expr.h>
#include <util/replace_symbol.h>
#include <util/std_expr.h>
#include <util/string2int.h>
#include <util/symbol_table.h>

#include "path_storage.h"

symex_configt::symex_configt(const optionst &options)
  : max_depth(options.get_unsigned_int_option("depth")),
    doing_path_exploration(options.is_set("paths")),
    allow_pointer_unsoundness(
      options.get_bool_option("allow-pointer-unsoundness")),
    constant_propagation(options.get_bool_option("propagation")),
    self_loops_to_assumptions(
      options.get_bool_option("self-loops-to-assumptions")),
    simplify_opt(options.get_bool_option("simplify")),
    unwinding_assertions(options.get_bool_option("unwinding-assertions")),
    partial_loops(options.get_bool_option("partial-loops")),
    havoc_undefined_functions(
      options.get_bool_option("havoc-undefined-functions")),
    debug_level(unsafe_string2int(options.get_option("debug-level"))),
    run_validation_checks(options.get_bool_option("validate-ssa-equation")),
    show_symex_steps(options.get_bool_option("show-goto-symex-steps")),
    show_points_to_sets(options.get_bool_option("show-points-to-sets")),
    max_field_sensitivity_array_size(
      options.is_set("no-array-field-sensitivity")
        ? 0
        : options.is_set("max-field-sensitivity-array-size")
            ? options.get_unsigned_int_option(
                "max-field-sensitivity-array-size")
            : DEFAULT_MAX_FIELD_SENSITIVITY_ARRAY_SIZE),
    complexity_limits_active(
      options.get_signed_int_option("symex-complexity-limit") > 0),
    cache_dereferences{options.get_bool_option("symex-cache-dereferences")}
{
}

/// If 'to' is not an instruction in our currently top-most active loop,
/// pop and re-check until we find an loop we're still active in, or empty
/// the stack.
static void pop_exited_loops(
  const goto_programt::const_targett &to,
  std::vector<framet::active_loop_infot> &active_loops)
{
  while(!active_loops.empty())
  {
    if(!active_loops.back().loop.contains(to))
      active_loops.pop_back();
    else
      break;
  }
}

void symex_transition(
  goto_symext::statet &state,
  goto_programt::const_targett to,
  bool is_backwards_goto)
{
  if(!state.call_stack().empty())
  {
    // initialize the loop counter of any loop we are newly entering
    // upon this transition; we are entering a loop if
    // 1. the transition from state.source.pc to "to" is not a backwards goto
    // or
    // 2. we are arriving from an outer loop

    // TODO: This should all be replaced by natural loop analysis.
    // This is because the way we detect loops is pretty imprecise.

    framet &frame = state.call_stack().top();
    const goto_programt::instructiont &instruction=*to;
    for(const auto &i_e : instruction.incoming_edges)
    {
      if(
        i_e->is_backwards_goto() && i_e->get_target() == to &&
        (!is_backwards_goto ||
         state.source.pc->location_number > i_e->location_number))
      {
        const auto loop_id =
          goto_programt::loop_id(state.source.function_id, *i_e);
        auto &current_loop_info = frame.loop_iterations[loop_id];
        current_loop_info.count = 0;

        // We've found a loop, put it on the stack and say it's our current
        // active loop.
        if(
          frame.loops_info && frame.loops_info->loop_map.find(to) !=
                                frame.loops_info->loop_map.end())
        {
          frame.active_loops.emplace_back(frame.loops_info->loop_map[to]);
        }
      }
    }

    // Only do this if we have active loop analysis going.
    if(!frame.active_loops.empty())
    {
      // Otherwise if we find we're transitioning out of a loop, make sure
      // to remove any loops we're not currently iterating over.

      // Match the do-while pattern.
      if(
        state.source.pc->is_backwards_goto() &&
        state.source.pc->location_number < to->location_number)
      {
        pop_exited_loops(to, frame.active_loops);
      }

      // Match for-each or while.
      for(const auto &incoming_edge : state.source.pc->incoming_edges)
      {
        if(
          incoming_edge->is_backwards_goto() &&
          incoming_edge->location_number < to->location_number)
        {
          pop_exited_loops(to, frame.active_loops);
        }
      }
    }
  }

  state.source.pc=to;
}

void symex_transition(goto_symext::statet &state)
{
  goto_programt::const_targett next = state.source.pc;
  ++next;
  symex_transition(state, next, false);
}

void goto_symext::symex_assert(
  const goto_programt::instructiont &instruction,
  statet &state)
{
  exprt condition = clean_expr(instruction.get_condition(), state, false);

  // First, push negations in and perhaps convert existential quantifiers into
  // universals:
  if(has_subexpr(condition, ID_exists) || has_subexpr(condition, ID_forall))
    do_simplify(condition);

  // Second, L2-rename universal quantifiers:
  if(has_subexpr(condition, ID_forall))
    rewrite_quantifiers(condition, state);

  // now rename, enables propagation
  exprt l2_condition = state.rename(std::move(condition), ns).get();

  // now try simplifier on it
  do_simplify(l2_condition);

  std::string msg = id2string(instruction.source_location().get_comment());
  if(msg.empty())
    msg = "assertion";

  vcc(l2_condition, msg, state);
}

void goto_symext::vcc(
  const exprt &condition,
  const std::string &msg,
  statet &state)
{
  state.total_vccs++;
  path_segment_vccs++;

  if(condition.is_true())
    return;

  const exprt guarded_condition = state.guard.guard_expr(condition);

  state.remaining_vccs++;
  target.assertion(state.guard.as_expr(), guarded_condition, msg, state.source);
}

void goto_symext::symex_assume(statet &state, const exprt &cond)
{
  exprt simplified_cond = clean_expr(cond, state, false);
  simplified_cond = state.rename(std::move(simplified_cond), ns).get();
  do_simplify(simplified_cond);

  // It would be better to call try_filter_value_sets after apply_condition,
  // but it is not currently possible. See the comment at the beginning of
  // \ref apply_goto_condition for more information.

  try_filter_value_sets(
    state, cond, state.value_set, &state.value_set, nullptr, ns);

  // apply_condition must come after rename because it might change the
  // constant propagator and the value-set and we read from those in rename
  state.apply_condition(simplified_cond, state, ns);

  symex_assume_l2(state, simplified_cond);
}

void goto_symext::symex_assume_l2(statet &state, const exprt &cond)
{
  if(cond.is_true())
    return;

  if(cond.is_false())
    state.reachable = false;

  // we are willing to re-write some quantified expressions
  exprt rewritten_cond = cond;
  if(has_subexpr(rewritten_cond, ID_exists))
    rewrite_quantifiers(rewritten_cond, state);

  if(state.threads.size()==1)
  {
    exprt tmp = state.guard.guard_expr(rewritten_cond);
    target.assumption(state.guard.as_expr(), tmp, state.source);
  }
  // symex_target_equationt::convert_assertions would fail to
  // consider assumptions of threads that have a thread-id above that
  // of the thread containing the assertion:
  // T0                     T1
  // x=0;                   assume(x==1);
  // assert(x!=42);         x=42;
  else
    state.guard.add(rewritten_cond);

  if(state.atomic_section_id!=0 &&
     state.guard.is_false())
    symex_atomic_end(state);
}

void goto_symext::rewrite_quantifiers(exprt &expr, statet &state)
{
  const bool is_assert = state.source.pc->is_assert();

  if(
    (is_assert && expr.id() == ID_forall) ||
    (!is_assert && expr.id() == ID_exists))
  {
    // for assertions e can rewrite "forall X. P" to "P", and
    // for assumptions we can rewrite "exists X. P" to "P"
    // we keep the quantified variable unique by means of L2 renaming
    auto &quant_expr = to_quantifier_expr(expr);
    symbol_exprt tmp0 =
      to_symbol_expr(to_ssa_expr(quant_expr.symbol()).get_original_expr());
    symex_decl(state, tmp0);
    instruction_local_symbols.push_back(tmp0);
    exprt tmp = quant_expr.where();
    rewrite_quantifiers(tmp, state);
    quant_expr.swap(tmp);
  }
  else if(expr.id() == ID_or || expr.id() == ID_and)
  {
    for(auto &op : expr.operands())
      rewrite_quantifiers(op, state);
  }
}

static void
switch_to_thread(goto_symex_statet &state, const unsigned int thread_nb)
{
  PRECONDITION(state.source.thread_nr < state.threads.size());
  PRECONDITION(thread_nb < state.threads.size());

  // save PC
  state.threads[state.source.thread_nr].pc = state.source.pc;
  state.threads[state.source.thread_nr].atomic_section_id =
    state.atomic_section_id;

  // get new PC
  state.source.thread_nr = thread_nb;
  state.source.pc = state.threads[thread_nb].pc;

  state.guard = state.threads[thread_nb].guard;
  // A thread's initial state is certainly reachable:
  state.reachable = true;
}

void goto_symext::symex_threaded_step(
  statet &state, const get_goto_functiont &get_goto_function)
{
  symex_step(get_goto_function, state);

  _total_vccs = state.total_vccs;
  _remaining_vccs = state.remaining_vccs;

  if(should_pause_symex)
    return;

  // is there another thread to execute?
  if(state.call_stack().empty() &&
     state.source.thread_nr+1<state.threads.size())
  {
    unsigned t=state.source.thread_nr+1;
#if 0
    std::cout << "********* Now executing thread " << t << '\n';
#endif
    switch_to_thread(state, t);
    symex_transition(state, state.source.pc, false);
  }
}

void goto_symext::symex_with_state(
  statet &state,
  const get_goto_functiont &get_goto_function,
  symbol_tablet &new_symbol_table)
{
  // resets the namespace to only wrap a single symbol table, and does so upon
  // destruction of an object of this type; instantiating the type is thus all
  // that's needed to achieve a reset upon exiting this method
  struct reset_namespacet
  {
    explicit reset_namespacet(namespacet &ns) : ns(ns)
    {
    }

    ~reset_namespacet()
    {
      // Get symbol table 1, the outer symbol table from the GOTO program
      const symbol_tablet &st = ns.get_symbol_table();
      // Move a new namespace containing this symbol table over the top of the
      // current one
      ns = namespacet(st);
    }

    namespacet &ns;
  };

  // We'll be using ns during symbolic execution and it needs to know
  // about the names minted in `state`, so make it point both to
  // `state`'s symbol table and the symbol table of the original
  // goto-program.
  ns = namespacet(outer_symbol_table, state.symbol_table);

  // whichever way we exit this method, reset the namespace back to a sane state
  // as state.symbol_table might go out of scope
  reset_namespacet reset_ns(ns);

  PRECONDITION(state.call_stack().top().end_of_function->is_end_function());

  symex_threaded_step(state, get_goto_function);
  if(should_pause_symex)
    return;
  while(!state.call_stack().empty())
  {
    state.has_saved_jump_target = false;
    state.has_saved_next_instruction = false;
    symex_threaded_step(state, get_goto_function);
    if(should_pause_symex)
      return;
  }

  // Clients may need to construct a namespace with both the names in
  // the original goto-program and the names generated during symbolic
  // execution, so return the names generated through symbolic execution
  // through `new_symbol_table`.
  new_symbol_table = state.symbol_table;
}

void goto_symext::resume_symex_from_saved_state(
  const get_goto_functiont &get_goto_function,
  const statet &saved_state,
  symex_target_equationt *const saved_equation,
  symbol_tablet &new_symbol_table)
{
  // saved_state contains a pointer to a symex_target_equationt that is
  // almost certainly stale. This is because equations are owned by bmcts,
  // and we construct a new bmct for every path that we execute. We're on a
  // new path now, so the old bmct and the equation that it owned have now
  // been deallocated. So, construct a new state from the old one, and make
  // its equation member point to the (valid) equation passed as an argument.
  statet state(saved_state, saved_equation);

  // Do NOT do the same initialization that `symex_with_state` does for a
  // fresh state, as that would clobber the saved state's program counter
  symex_with_state(
      state,
      get_goto_function,
      new_symbol_table);
}

std::unique_ptr<goto_symext::statet> goto_symext::initialize_entry_point_state(
  const get_goto_functiont &get_goto_function)
{
  const irep_idt entry_point_id = goto_functionst::entry_point();

  const goto_functionst::goto_functiont *start_function;
  try
  {
    start_function = &get_goto_function(entry_point_id);
  }
  catch(const std::out_of_range &)
  {
    throw unsupported_operation_exceptiont("the program has no entry point");
  }

  // Get our path_storage pointer because this state will live beyond
  // this instance of goto_symext, so we can't take the reference directly.
  auto *storage = &path_storage;

  // create and prepare the state
  auto state = util_make_unique<statet>(
    symex_targett::sourcet(entry_point_id, start_function->body),
    symex_config.max_field_sensitivity_array_size,
    guard_manager,
    [storage](const irep_idt &id) { return storage->get_unique_l2_index(id); });

  CHECK_RETURN(!state->threads.empty());
  CHECK_RETURN(!state->call_stack().empty());

  goto_programt::const_targett limit =
    std::prev(start_function->body.instructions.end());
  state->call_stack().top().end_of_function = limit;
  state->call_stack().top().calling_location.pc =
    state->call_stack().top().end_of_function;
  state->call_stack().top().hidden_function = start_function->is_hidden();

  state->symex_target = &target;

  state->run_validation_checks = symex_config.run_validation_checks;

  // initialize support analyses
  auto emplace_safe_pointers_result =
    path_storage.safe_pointers.emplace(entry_point_id, local_safe_pointerst{});
  if(emplace_safe_pointers_result.second)
    emplace_safe_pointers_result.first->second(start_function->body);

  path_storage.dirty.populate_dirty_for_function(
    entry_point_id, *start_function);
  state->dirty = &path_storage.dirty;

  // Only enable loop analysis when complexity is enabled.
  if(symex_config.complexity_limits_active)
  {
    // Set initial loop analysis.
    path_storage.add_function_loops(entry_point_id, start_function->body);
    state->call_stack().top().loops_info =
      path_storage.get_loop_analysis(entry_point_id);
  }

  // make the first step onto the instruction pointed to by the initial program
  // counter
  symex_transition(*state, state->source.pc, false);

  return state;
}

void goto_symext::symex_from_entry_point_of(
  const get_goto_functiont &get_goto_function,
  symbol_tablet &new_symbol_table)
{
  auto state = initialize_entry_point_state(get_goto_function);

  symex_with_state(*state, get_goto_function, new_symbol_table);
}

void goto_symext::initialize_path_storage_from_entry_point_of(
  const get_goto_functiont &get_goto_function,
  symbol_tablet &new_symbol_table)
{
  auto state = initialize_entry_point_state(get_goto_function);

  path_storaget::patht entry_point_start(target, *state);
  entry_point_start.state.saved_target = state->source.pc;
  entry_point_start.state.has_saved_next_instruction = true;

  path_storage.push(entry_point_start);
}

goto_symext::get_goto_functiont
goto_symext::get_goto_function(abstract_goto_modelt &goto_model)
{
  return [&goto_model](
           const irep_idt &id) -> const goto_functionst::goto_functiont & {
    return goto_model.get_goto_function(id);
  };
}

messaget::mstreamt &
goto_symext::print_callstack_entry(const symex_targett::sourcet &source)
{
  log.status() << source.function_id
               << " location number: " << source.pc->location_number;

  return log.status();
}

void goto_symext::print_symex_step(statet &state)
{
  // If we're showing the route, begin outputting debug info, and don't print
  // instructions we don't run.

  // We also skip dead instructions as they don't add much to step-based
  // debugging and if there's no code block at this point.
  if(
    !symex_config.show_symex_steps || !state.reachable ||
    state.source.pc->type() == DEAD ||
    (state.source.pc->get_code().is_nil() &&
     state.source.pc->type() != END_FUNCTION))
  {
    return;
  }

  if(state.source.pc->get_code().is_not_nil())
  {
    auto guard_expression = state.guard.as_expr();
    std::size_t size = 0;
    for(auto it = guard_expression.depth_begin();
        it != guard_expression.depth_end();
        ++it)
    {
      size++;
    }

    log.status() << "[Guard size: " << size << "] "
                 << format(state.source.pc->get_code());

    if(
      state.source.pc->source_location().is_not_nil() &&
      !state.source.pc->source_location().get_java_bytecode_index().empty())
    {
      log.status()
        << " bytecode index: "
        << state.source.pc->source_location().get_java_bytecode_index();
    }

    log.status() << messaget::eom;
  }

  // Print the method we're returning too.
  const auto &call_stack = state.threads[state.source.thread_nr].call_stack;
  if(state.source.pc->type() == END_FUNCTION)
  {
    log.status() << messaget::eom;

    if(!call_stack.empty())
    {
      log.status() << "Returning to: ";
      print_callstack_entry(call_stack.back().calling_location)
        << messaget::eom;
    }

    log.status() << messaget::eom;
  }

  // On a function call print the entire call stack.
  if(state.source.pc->type() == FUNCTION_CALL)
  {
    log.status() << messaget::eom;

    if(!call_stack.empty())
    {
      log.status() << "Call stack:" << messaget::eom;

      for(auto &frame : call_stack)
      {
        print_callstack_entry(frame.calling_location) << messaget::eom;
      }

      print_callstack_entry(state.source) << messaget::eom;

      // Add the method we're about to enter with no location number.
      log.status() << format(state.source.pc->call_function()) << messaget::eom
                   << messaget::eom;
    }
  }
}

/// do just one step
void goto_symext::symex_step(
  const get_goto_functiont &get_goto_function,
  statet &state)
{
  // Print debug statements if they've been enabled.
  print_symex_step(state);
  execute_next_instruction(get_goto_function, state);
  kill_instruction_local_symbols(state);
}

void goto_symext::execute_next_instruction(
  const get_goto_functiont &get_goto_function,
  statet &state)
{
  PRECONDITION(!state.threads.empty());
  PRECONDITION(!state.call_stack().empty());

  const goto_programt::instructiont &instruction=*state.source.pc;

  if(!symex_config.doing_path_exploration)
    merge_gotos(state);

  // depth exceeded?
  if(state.depth > symex_config.max_depth)
  {
    // Rule out this path:
    symex_assume_l2(state, false_exprt());
  }
  state.depth++;

  // actually do instruction
  switch(instruction.type())
  {
  case SKIP:
    if(state.reachable)
      target.location(state.guard.as_expr(), state.source);
    symex_transition(state);
    break;

  case END_FUNCTION:
    // do even if !state.reachable to clear out frame created
    // in symex_start_thread
    symex_end_of_function(state);
    symex_transition(state);
    break;

  case LOCATION:
    if(state.reachable)
      target.location(state.guard.as_expr(), state.source);
    symex_transition(state);
    break;

  case GOTO:
    if(state.reachable)
      symex_goto(state);
    else
      symex_unreachable_goto(state);
    break;

  case ASSUME:
    if(state.reachable)
      symex_assume(state, instruction.get_condition());
    symex_transition(state);
    break;

  case ASSERT:
    if(state.reachable && !ignore_assertions)
      symex_assert(instruction, state);
    symex_transition(state);
    break;

  case SET_RETURN_VALUE:
    // This case should have been removed by return-value removal
    UNREACHABLE;
    break;

  case ASSIGN:
    if(state.reachable)
      symex_assign(state, instruction.assign_lhs(), instruction.assign_rhs());

    symex_transition(state);
    break;

  case FUNCTION_CALL:
    if(state.reachable)
      symex_function_call(get_goto_function, state, instruction);
    else
      symex_transition(state);
    break;

  case OTHER:
    if(state.reachable)
      symex_other(state);
    symex_transition(state);
    break;

  case DECL:
    if(state.reachable)
      symex_decl(state);
    symex_transition(state);
    break;

  case DEAD:
    symex_dead(state);
    symex_transition(state);
    break;

  case START_THREAD:
    symex_start_thread(state);
    symex_transition(state);
    break;

  case END_THREAD:
    // behaves like assume(0);
    if(state.reachable)
      state.reachable = false;
    symex_transition(state);
    break;

  case ATOMIC_BEGIN:
    symex_atomic_begin(state);
    symex_transition(state);
    break;

  case ATOMIC_END:
    symex_atomic_end(state);
    symex_transition(state);
    break;

  case CATCH:
    symex_catch(state);
    symex_transition(state);
    break;

  case THROW:
    symex_throw(state);
    symex_transition(state);
    break;

  case NO_INSTRUCTION_TYPE:
    throw unsupported_operation_exceptiont("symex got NO_INSTRUCTION");

  case INCOMPLETE_GOTO:
    DATA_INVARIANT(false, "symex got unexpected instruction type");
  }

  complexity_violationt complexity_result =
    complexity_module.check_complexity(state);
  if(complexity_result != complexity_violationt::NONE)
    complexity_module.run_transformations(complexity_result, state);
}

void goto_symext::kill_instruction_local_symbols(statet &state)
{
  for(const auto &symbol_expr : instruction_local_symbols)
    symex_dead(state, symbol_expr);
  instruction_local_symbols.clear();
}

/// Check if an expression only contains one unique symbol (possibly repeated
/// multiple times)
/// \param expr: The expression to examine
/// \return If only one unique symbol occurs in \p expr then return it;
///   otherwise return an empty optionalt
static optionalt<symbol_exprt>
find_unique_pointer_typed_symbol(const exprt &expr)
{
  optionalt<symbol_exprt> return_value;
  for(auto it = expr.depth_cbegin(); it != expr.depth_cend(); ++it)
  {
    const symbol_exprt *symbol_expr = expr_try_dynamic_cast<symbol_exprt>(*it);
    if(symbol_expr && can_cast_type<pointer_typet>(symbol_expr->type()))
    {
      // If we already have a potential return value, check if it is the same
      // symbol, and return an empty optionalt if not
      if(return_value && *symbol_expr != *return_value)
      {
        return {};
      }
      return_value = *symbol_expr;
    }
  }

  // Either expr contains no pointer-typed symbols or it contains one unique
  // pointer-typed symbol, possibly repeated multiple times
  return return_value;
}

void goto_symext::try_filter_value_sets(
  goto_symex_statet &state,
  exprt condition,
  const value_sett &original_value_set,
  value_sett *jump_taken_value_set,
  value_sett *jump_not_taken_value_set,
  const namespacet &ns)
{
  condition = state.rename<L1>(std::move(condition), ns).get();

  optionalt<symbol_exprt> symbol_expr =
    find_unique_pointer_typed_symbol(condition);

  if(!symbol_expr)
  {
    return;
  }

  const pointer_typet &symbol_type = to_pointer_type(symbol_expr->type());

  const std::vector<exprt> value_set_elements =
    original_value_set.get_value_set(*symbol_expr, ns);

  std::unordered_set<exprt, irep_hash> erase_from_jump_taken_value_set;
  std::unordered_set<exprt, irep_hash> erase_from_jump_not_taken_value_set;
  erase_from_jump_taken_value_set.reserve(value_set_elements.size());
  erase_from_jump_not_taken_value_set.reserve(value_set_elements.size());

  // Try evaluating the condition with the symbol replaced by a pointer to each
  // one of its possible values in turn. If that leads to a true for some
  // value_set_element then we can delete it from the value set that will be
  // used if the condition is false, and vice versa.
  for(const exprt &value_set_element : value_set_elements)
  {
    if(
      value_set_element.id() == ID_unknown ||
      value_set_element.id() == ID_invalid)
    {
      continue;
    }

    const bool exclude_null_derefs = false;
    if(value_set_dereferencet::should_ignore_value(
         value_set_element, exclude_null_derefs, language_mode))
    {
      continue;
    }

    value_set_dereferencet::valuet value =
      value_set_dereferencet::build_reference_to(
        value_set_element, *symbol_expr, ns);

    if(value.pointer.is_nil())
      continue;

    exprt modified_condition(condition);

    address_of_aware_replace_symbolt replace_symbol{};
    replace_symbol.insert(*symbol_expr, value.pointer);
    replace_symbol(modified_condition);

    // This do_simplify() is needed for the following reason: if `condition` is
    // `*p == a` and we replace `p` with `&a` then we get `*&a == a`. Suppose
    // our constant propagation knows that `a` is `1`. Without this call to
    // do_simplify(), state.rename() turns this into `*&a == 1` (because
    // rename() doesn't do constant propagation inside addresses), which
    // do_simplify() turns into `a == 1`, which cannot be evaluated as true
    // without another round of constant propagation.
    // It would be sufficient to replace this call to do_simplify() with
    // something that just replaces `*&x` with `x` whenever it finds it.
    do_simplify(modified_condition);

    state.record_events.push(false);
    modified_condition = state.rename(std::move(modified_condition), ns).get();
    state.record_events.pop();

    do_simplify(modified_condition);

    if(jump_taken_value_set && modified_condition.is_false())
    {
      erase_from_jump_taken_value_set.insert(value_set_element);
    }
    else if(jump_not_taken_value_set && modified_condition.is_true())
    {
      erase_from_jump_not_taken_value_set.insert(value_set_element);
    }
  }
  if(jump_taken_value_set && !erase_from_jump_taken_value_set.empty())
  {
    auto entry_index = jump_taken_value_set->get_index_of_symbol(
      symbol_expr->get_identifier(), symbol_type, "", ns);
    jump_taken_value_set->erase_values_from_entry(
      *entry_index, erase_from_jump_taken_value_set);
  }
  if(jump_not_taken_value_set && !erase_from_jump_not_taken_value_set.empty())
  {
    auto entry_index = jump_not_taken_value_set->get_index_of_symbol(
      symbol_expr->get_identifier(), symbol_type, "", ns);
    jump_not_taken_value_set->erase_values_from_entry(
      *entry_index, erase_from_jump_not_taken_value_set);
  }
}
