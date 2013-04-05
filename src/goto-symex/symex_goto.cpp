/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <expr_util.h>
#include <std_expr.h>
#include <i2string.h>

#include "goto_symex.h"

/*******************************************************************\

Function: goto_symext::symex_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_goto(statet &state)
{
  const goto_programt::instructiont &instruction=*state.source.pc;
  
  exprt old_guard=instruction.guard;
  dereference(old_guard, state, false);

  exprt new_guard=old_guard;
  state.rename(new_guard, ns);
  do_simplify(new_guard);
  
  target.location(state.guard.as_expr(), state.source);
  
  if(new_guard.is_false() ||
     state.guard.is_false())
  {
    // reset unwinding counter
    unwind_map[state.source]=0;

    // next instruction
    state.source.pc++;
    return; // nothing to do
  }
    
  assert(!instruction.targets.empty());
  
  // we only do deterministic gotos for now
  if(instruction.targets.size()!=1)
    throw "no support for non-deterministic gotos";
    
  goto_programt::const_targett goto_target=
    instruction.targets.front();
    
  bool forward=
    state.source.pc->location_number<
    goto_target->location_number;
    
  if(!forward) // backwards?
  {
    unsigned &unwind=unwind_map[state.source];
    unwind++;
    
    if(get_unwind(state.source, unwind))
    {
      loop_bound_exceeded(state, new_guard);

      // reset unwinding
      unwind_map[state.source]=0;
      
      // next instruction
      state.source.pc++;
      return;
    }      
  
    if(new_guard.is_true())
    {
      state.source.pc=goto_target;
      return; // nothing else to do
    }
  }
  
  goto_programt::const_targett new_state_pc, state_pc;
  
  if(forward)
  {
    new_state_pc=goto_target;
    state_pc=state.source.pc;
    state_pc++;
  }
  else
  {
    new_state_pc=state.source.pc;
    new_state_pc++;
    state_pc=goto_target;
  }

  state.source.pc=state_pc;
  
  // put into state-queue
  statet::goto_state_listt &goto_state_list=
    state.top().goto_state_map[new_state_pc];

  goto_state_list.push_back(statet::goto_statet(state));
  statet::goto_statet &new_state=goto_state_list.back();
  
  // adjust guards
  if(new_guard.is_true())
  {
    state.guard.make_false();
  }
  else
  {
    // produce new guard symbol
    exprt guard_expr;

    if(new_guard.id()==ID_symbol ||
       (new_guard.id()==ID_not &&
        new_guard.operands().size()==1 &&
        new_guard.op0().id()==ID_symbol))
      guard_expr=new_guard;
    else
    {
      symbol_exprt guard_symbol_expr=
        symbol_exprt(guard_identifier, bool_typet());
      exprt new_rhs=new_guard;
      new_rhs.make_not();
      
      symbol_exprt new_lhs=guard_symbol_expr;
      state.rename(new_lhs, ns, goto_symex_statet::L1);
      state.assignment(new_lhs, new_rhs, ns, false);
      
      guardt guard;

      target.assignment(
        guard.as_expr(),
        new_lhs, guard_symbol_expr, new_lhs, guard_symbol_expr,
        new_rhs,
        state.source,
        symex_targett::GUARD);
      
      guard_expr=guard_symbol_expr;
      guard_expr.make_not();
      state.rename(guard_expr, ns);
    }
    
    if(forward)
    {
      new_state.guard.add(guard_expr);
      guard_expr.make_not();
      state.guard.add(guard_expr);
    }
    else
    {
      state.guard.add(guard_expr);
      guard_expr.make_not();
      new_state.guard.add(guard_expr);
    }
  }
}

/*******************************************************************\

Function: goto_symext::symex_step_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_step_goto(statet &state, bool taken)
{
  const goto_programt::instructiont &instruction=*state.source.pc;
  
  exprt guard(instruction.guard);
  dereference(guard, state, false);
  state.rename(guard, ns);
  
  if(!taken) guard.make_not();
  
  state.guard.guard_expr(guard);
  do_simplify(guard);

  target.assumption(state.guard.as_expr(), guard, state.source);  
}

/*******************************************************************\

Function: goto_symext::merge_gotos

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::merge_gotos(statet &state)
{
  statet::framet &frame=state.top();
  
  // first, see if this is a target at all
  statet::goto_state_mapt::iterator state_map_it=
    frame.goto_state_map.find(state.source.pc);
  
  if(state_map_it==frame.goto_state_map.end())
    return; // nothing to do

  // we need to merge
  statet::goto_state_listt &state_list=state_map_it->second;

  for(statet::goto_state_listt::reverse_iterator
      list_it=state_list.rbegin();
      list_it!=state_list.rend();
      list_it++)
  {
    statet::goto_statet &goto_state=*list_it;
    
    // do SSA phi functions
    phi_function(goto_state, state);

    merge_value_sets(goto_state, state);

    // adjust guard
    state.guard|=goto_state.guard;

    // adjust depth
    state.depth=std::min(state.depth, goto_state.depth);
  }
  
  // clean up to save some memory
  frame.goto_state_map.erase(state_map_it);
}

/*******************************************************************\

Function: goto_symext::merge_value_sets

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::merge_value_sets(
  const statet::goto_statet &src,
  statet &dest)
{
  if(dest.guard.is_false())
  {
    dest.value_set=src.value_set;
    return;
  }
  
  dest.value_set.make_union(src.value_set);
}

/*******************************************************************\

Function: goto_symext::phi_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::phi_function(
  const statet::goto_statet &goto_state,
  statet &dest_state)
{
  // go over all variables to see what changed
  std::set<irep_idt> variables;

  goto_state.level2.get_variables(variables);
  dest_state.level2.get_variables(variables);
  
  for(std::set<irep_idt>::const_iterator
      it=variables.begin();
      it!=variables.end();
      it++)
  {
    const irep_idt l1_identifier=*it;
  
    if(l1_identifier==guard_identifier)
      continue; // just a guard, don't bother
      
    if(goto_state.level2.current_count(l1_identifier)==
       dest_state.level2.current_count(l1_identifier))
      continue; // not at all changed

    // changed!

    irep_idt original_identifier=
      dest_state.get_original_name(l1_identifier);

    // get type (may need renaming)      
    const symbolt &symbol=ns.lookup(original_identifier);
    
    // shared?
    if(dest_state.threads.size()>=2 && symbol.is_shared())
      continue; // no phi nodes for shared stuff
    
    typet type=symbol.type;
    dest_state.rename(type, ns);
    
    exprt goto_state_rhs, dest_state_rhs;

    {
      goto_symex_statet::propagationt::valuest::const_iterator p_it=
        goto_state.propagation.values.find(l1_identifier);

      if(p_it!=goto_state.propagation.values.end())
        goto_state_rhs=p_it->second;
      else
        goto_state_rhs=symbol_exprt(goto_state.level2.current_name(l1_identifier), type);
    }
    
    {
      goto_symex_statet::propagationt::valuest::const_iterator p_it=
        dest_state.propagation.values.find(l1_identifier);

      if(p_it!=dest_state.propagation.values.end())
        dest_state_rhs=p_it->second;
      else
        dest_state_rhs=symbol_exprt(dest_state.level2.current_name(l1_identifier), type);
    }
    
    exprt rhs;
    
    if(dest_state.guard.is_false())
      rhs=goto_state_rhs;
    else if(goto_state.guard.is_false())
      rhs=dest_state_rhs;
    else
    {      
      guardt tmp_guard(goto_state.guard);
      
      // this gets the diff between the guards
      tmp_guard-=dest_state.guard;
      
      rhs=if_exprt(tmp_guard.as_expr(), goto_state_rhs, dest_state_rhs, type);
    }

    symbol_exprt lhs=symbol_expr(symbol);
    symbol_exprt new_lhs=symbol_exprt(l1_identifier, type);
    dest_state.assignment(new_lhs, rhs, ns, true);
    
    target.assignment(
      true_exprt(),
      new_lhs, lhs, new_lhs, lhs,
      rhs,
      dest_state.source,
      symex_targett::PHI);
  }
}

/*******************************************************************\

Function: goto_symext::loop_bound_exceeded

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::loop_bound_exceeded(
  statet &state,
  const exprt &guard)
{
  const unsigned loop_number=state.source.pc->loop_number;
    
  exprt negated_cond;

  if(guard.is_true())
    negated_cond=false_exprt();
  else
    negated_cond=gen_not(guard);

  bool unwinding_assertions=
    options.get_bool_option("unwinding-assertions");
    
  bool partial_loops=
    options.get_bool_option("partial-loops");
  
  if(!partial_loops)
  {
    if(unwinding_assertions)
    {
      // Generate unwinding assertion.
      claim(negated_cond,
            "unwinding assertion loop "+i2string(loop_number),
            state);
    }
    else
    {
      // generate unwinding assumption, unless we permit partial loops
      exprt guarded_expr=negated_cond;
      state.guard.guard_expr(guarded_expr);
      target.assumption(state.guard.as_expr(), guarded_expr, state.source);
    }

    // add to state guard to prevent further assignments
    state.guard.add(negated_cond);
  }
}

/*******************************************************************\

Function: goto_symext::get_unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool goto_symext::get_unwind(
  const symex_targett::sourcet &source,
  unsigned unwind)
{
  return false;
}
