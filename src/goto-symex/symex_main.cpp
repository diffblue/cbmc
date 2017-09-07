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
        frame.loop_iterations[goto_programt::loop_id(i_e)].count=0;
  }

  state.source.pc=to;
}

void goto_symext::new_name(symbolt &symbol)
{
  get_new_name(symbol, ns);
  new_symbol_table.add(symbol);
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
    assert(expr.operands().size()==2);
    assert(expr.op0().id()==ID_symbol);
    symbol_exprt tmp0=
      to_symbol_expr(to_ssa_expr(expr.op0()).get_original_expr());
    symex_decl(state, tmp0);
    exprt tmp=expr.op1();
    expr.swap(tmp);
  }
}

/// symex from given state
void goto_symext::operator()(
  statet &state,
  const goto_functionst &goto_functions,
  const goto_programt &goto_program)
{
  assert(!goto_program.instructions.empty());

  state.source=symex_targett::sourcet(goto_program);
  assert(!state.threads.empty());
  assert(!state.call_stack().empty());
  state.top().end_of_function=--goto_program.instructions.end();
  state.top().calling_location.pc=state.top().end_of_function;
  state.symex_target=&target;
  state.dirty=util_make_unique<dirtyt>(goto_functions);

  symex_transition(state, state.source.pc);

  assert(state.top().end_of_function->is_end_function());

  while(!state.call_stack().empty())
  {
    symex_step(goto_functions, state);

    // is there another thread to execute?
    if(state.call_stack().empty() &&
       state.source.thread_nr+1<state.threads.size())
    {
      unsigned t=state.source.thread_nr+1;
      // std::cout << "********* Now executing thread " << t << '\n';
      state.switch_to_thread(t);
      symex_transition(state, state.source.pc);
    }
  }

  state.dirty=nullptr;
}

/// symex starting from given program
void goto_symext::operator()(
  const goto_functionst &goto_functions,
  const goto_programt &goto_program)
{
  statet state;
  operator() (state, goto_functions, goto_program);
}

/// symex from entry point
void goto_symext::operator()(const goto_functionst &goto_functions)
{
  goto_functionst::function_mapt::const_iterator it=
    goto_functions.function_map.find(goto_functionst::entry_point());

  if(it==goto_functions.function_map.end())
    throw "the program has no entry point";

  const goto_programt &body=it->second.body;

  operator()(goto_functions, body);
}

/// do just one step
void goto_symext::symex_step(
  const goto_functionst &goto_functions,
  statet &state)
{
  #if 0
  std::cout << "\ninstruction type is " << state.source.pc->type << '\n';
  std::cout << "Location: " << state.source.pc->source_location << '\n';
  std::cout << "Guard: " << from_expr(ns, "", state.guard.as_expr()) << '\n';
  std::cout << "Code: " << from_expr(ns, "", state.source.pc->code) << '\n';
  #endif

  assert(!state.threads.empty());
  assert(!state.call_stack().empty());

  const goto_programt::instructiont &instruction=*state.source.pc;

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
      symex_assign_rec(state, to_code_assign(instruction.code));

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

      symex_function_call(goto_functions, state, deref_code);
    }
    else
      symex_transition(state);
    break;

  case OTHER:
    if(!state.guard.is_false())
      symex_other(goto_functions, state);

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
