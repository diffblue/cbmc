/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <cassert>
#include <memory>

#include <util/std_expr.h>
#include <util/rename.h>
#include <util/symbol_table.h>
#include <util/replace_symbol.h>
#include <util/make_unique.h>

#include <analyses/dirty.h>

void goto_symext::symex_transition(
  statet &state,
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
    statet::framet &frame=state.top();
    const goto_programt::instructiont &instruction=*to;
    for(const auto &i_e : instruction.incoming_edges)
      if(i_e->is_goto() && i_e->is_backwards_goto() &&
         (!is_backwards_goto ||
          state.source.pc->location_number>i_e->location_number))
        frame.loop_iterations[goto_programt::loop_id(*i_e)].count=0;
  }

  state.source.pc=to;
}

void goto_symext::new_name(symbolt &symbol, statet &state)
{
  get_new_name(symbol, ns);
  state.symbol_table.add(symbol);
}

void goto_symext::vcc(
  const exprt &vcc_expr,
  const std::string &msg,
  statet &state)
{
  total_vccs++;

  exprt expr=vcc_expr;

  // we are willing to re-write some quantified expressions
  rewrite_quantifiers(expr, state);

  // now rename, enables propagation
  state.rename(expr, ns);

  // now try simplifier on it
  do_simplify(expr);

  if(expr.is_true())
    return;

  state.guard.guard_expr(expr);

  remaining_vccs++;
  target.assertion(state.guard.as_expr(), expr, msg, state.source);
}

void goto_symext::symex_assume(statet &state, const exprt &cond)
{
  exprt simplified_cond=cond;

  do_simplify(simplified_cond);

  if(simplified_cond.is_true())
    return;

  if(state.threads.size()==1)
  {
    exprt tmp=simplified_cond;
    state.guard.guard_expr(tmp);
    target.assumption(state.guard.as_expr(), tmp, state.source);
  }
  // symex_target_equationt::convert_assertions would fail to
  // consider assumptions of threads that have a thread-id above that
  // of the thread containing the assertion:
  // T0                     T1
  // x=0;                   assume(x==1);
  // assert(x!=42);         x=42;
  else
    state.guard.add(simplified_cond);

  if(state.atomic_section_id!=0 &&
     state.guard.is_false())
    symex_atomic_end(state);
}

void goto_symext::rewrite_quantifiers(exprt &expr, statet &state)
{
  if(expr.id()==ID_forall)
  {
    // forall X. P -> P
    // we keep the quantified variable unique by means of L2 renaming
    PRECONDITION(expr.operands().size()==2);
    PRECONDITION(expr.op0().id()==ID_symbol);
    symbol_exprt tmp0=
      to_symbol_expr(to_ssa_expr(expr.op0()).get_original_expr());
    symex_decl(state, tmp0);
    exprt tmp=expr.op1();
    expr.swap(tmp);
  }
}

void goto_symext::initialize_entry_point(
  statet &state,
  const get_goto_functiont &get_goto_function,
  const goto_programt::const_targett pc,
  const goto_programt::const_targett limit)
{
  PRECONDITION(!state.threads.empty());
  PRECONDITION(!state.call_stack().empty());
  state.source=symex_targett::sourcet(pc);
  state.top().end_of_function=limit;
  state.top().calling_location.pc=state.top().end_of_function;
  state.symex_target=&target;

  INVARIANT(
    !pc->function.empty(), "all symexed instructions should have a function");
  state.dirty.populate_dirty_for_function(
    pc->function, get_goto_function(pc->function));

  symex_transition(state, state.source.pc);
}

void goto_symext::symex_threaded_step(
  statet &state, const get_goto_functiont &get_goto_function)
{
  symex_step(get_goto_function, state);

  // is there another thread to execute?
  if(state.call_stack().empty() &&
     state.source.thread_nr+1<state.threads.size())
  {
    unsigned t=state.source.thread_nr+1;
#if 0
    std::cout << "********* Now executing thread " << t << '\n';
#endif
    state.switch_to_thread(t);
    symex_transition(state, state.source.pc);
  }
}

static goto_symext::get_goto_functiont get_function_from_goto_functions(
  const goto_functionst &goto_functions)
{
  return [&goto_functions](const irep_idt &key) ->
    const goto_functionst::goto_functiont & { // NOLINT(*)
    return goto_functions.function_map.at(key);
  };
}

void goto_symext::symex_with_state(
  statet &state,
  const goto_functionst &goto_functions,
  symbol_tablet &new_symbol_table)
{
  symex_with_state(
    state,
    get_function_from_goto_functions(goto_functions),
    new_symbol_table);
}

void goto_symext::symex_with_state(
  statet &state,
  const get_goto_functiont &get_goto_function,
  symbol_tablet &new_symbol_table)
{
  // We'll be using ns during symbolic execution and it needs to know
  // about the names minted in `state`, so make it point both to
  // `state`'s symbol table and the symbol table of the original
  // goto-program.
  ns = namespacet(outer_symbol_table, state.symbol_table);

  PRECONDITION(state.top().end_of_function->is_end_function());

  symex_threaded_step(state, get_goto_function);
  while(!state.call_stack().empty())
  {
    state.has_saved_target = false;
    symex_threaded_step(state, get_goto_function);
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

  symex_transition(state, state.source.pc);
  // Do NOT do the same initialization that `symex_with_state` does for a
  // fresh state, as that would clobber the saved state's program counter
  symex_with_state(
      state,
      get_goto_function,
      new_symbol_table);
}

void goto_symext::symex_instruction_range(
  statet &state,
  const goto_functionst &goto_functions,
  const goto_programt::const_targett first,
  const goto_programt::const_targett limit)
{
  symex_instruction_range(
    state, get_function_from_goto_functions(goto_functions), first, limit);
}

void goto_symext::symex_instruction_range(
  statet &state,
  const get_goto_functiont &get_goto_function,
  const goto_programt::const_targett first,
  const goto_programt::const_targett limit)
{
  initialize_entry_point(state, get_goto_function, first, limit);
  ns = namespacet(outer_symbol_table, state.symbol_table);
  while(state.source.pc->function!=limit->function || state.source.pc!=limit)
    symex_threaded_step(state, get_goto_function);
}

void goto_symext::symex_from_entry_point_of(
  const goto_functionst &goto_functions,
  symbol_tablet &new_symbol_table)
{
  symex_from_entry_point_of(
    get_function_from_goto_functions(goto_functions), new_symbol_table);
}

void goto_symext::symex_from_entry_point_of(
  const get_goto_functiont &get_goto_function,
  symbol_tablet &new_symbol_table)
{
  const goto_functionst::goto_functiont *start_function;
  try
  {
    start_function = &get_goto_function(goto_functionst::entry_point());
  }
  catch(const std::out_of_range &error)
  {
    throw "the program has no entry point";
  }

  statet state;

  initialize_entry_point(
    state,
    get_goto_function,
    start_function->body.instructions.begin(),
    prev(start_function->body.instructions.end()));

  symex_with_state(
    state, get_goto_function, new_symbol_table);
}

/// do just one step
void goto_symext::symex_step(
  const get_goto_functiont &get_goto_function,
  statet &state)
{
  #if 0
  std::cout << "\ninstruction type is " << state.source.pc->type << '\n';
  std::cout << "Location: " << state.source.pc->source_location << '\n';
  std::cout << "Guard: " << from_expr(ns, "", state.guard.as_expr()) << '\n';
  std::cout << "Code: " << from_expr(ns, "", state.source.pc->code) << '\n';
  #endif

  PRECONDITION(!state.threads.empty());
  PRECONDITION(!state.call_stack().empty());

  const goto_programt::instructiont &instruction=*state.source.pc;

  if(!options.get_bool_option("paths"))
    merge_gotos(state);

  // depth exceeded?
  {
    unsigned max_depth=options.get_unsigned_int_option("depth");
    if(max_depth!=0 && state.depth>max_depth)
      state.guard.add(false_exprt());
    state.depth++;
  }

  // actually do instruction
  switch(instruction.type)
  {
  case SKIP:
    if(!state.guard.is_false())
      target.location(state.guard.as_expr(), state.source);
    symex_transition(state);
    break;

  case END_FUNCTION:
    // do even if state.guard.is_false() to clear out frame created
    // in symex_start_thread
    symex_end_of_function(state);
    symex_transition(state);
    break;

  case LOCATION:
    if(!state.guard.is_false())
      target.location(state.guard.as_expr(), state.source);
    symex_transition(state);
    break;

  case GOTO:
    symex_goto(state);
    break;

  case ASSUME:
    if(!state.guard.is_false())
    {
      exprt tmp=instruction.guard;
      clean_expr(tmp, state, false);
      state.rename(tmp, ns);
      symex_assume(state, tmp);
    }

    symex_transition(state);
    break;

  case ASSERT:
    if(!state.guard.is_false())
    {
      std::string msg=id2string(state.source.pc->source_location.get_comment());
      if(msg=="")
        msg="assertion";
      exprt tmp(instruction.guard);
      clean_expr(tmp, state, false);
      vcc(tmp, msg, state);
    }

    symex_transition(state);
    break;

  case RETURN:
    if(!state.guard.is_false())
      return_assignment(state);

    symex_transition(state);
    break;

  case ASSIGN:
    if(!state.guard.is_false())
      symex_assign(state, to_code_assign(instruction.code));

    symex_transition(state);
    break;

  case FUNCTION_CALL:
    if(!state.guard.is_false())
    {
      code_function_callt deref_code=
        to_code_function_call(instruction.code);

      if(deref_code.lhs().is_not_nil())
        clean_expr(deref_code.lhs(), state, true);

      clean_expr(deref_code.function(), state, false);

      Forall_expr(it, deref_code.arguments())
        clean_expr(*it, state, false);

      symex_function_call(get_goto_function, state, deref_code);
    }
    else
      symex_transition(state);
    break;

  case OTHER:
    if(!state.guard.is_false())
      symex_other(state);

    symex_transition(state);
    break;

  case DECL:
    if(!state.guard.is_false())
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
    if(!state.guard.is_false())
      state.guard.add(false_exprt());
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
    throw "symex got NO_INSTRUCTION";

  default:
    throw "symex got unexpected instruction";
  }
}
