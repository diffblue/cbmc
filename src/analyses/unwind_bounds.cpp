/*******************************************************************\

Module: Compute unwind bounds

Author: Daniel Poetzl

\*******************************************************************/

/// \file
/// Compute unwind bounds

#include "unwind_bounds.h"

//#define DEBUG
//#define DEBUG_VERBOSE

#if defined(DEBUG) || defined(DEBUG_VERBOSE)
#include <iostream>
#endif

void unwind_boundst::output(std::ostream &out) const
{
  out << "Unwind bounds:\n";

  for(loop_sett::const_iterator l_it=all_loops.begin();
      l_it!=all_loops.end(); l_it++)
  {
    const locationt loop=*l_it;
    const goto_programt &goto_program=get_goto_program(loop);

    irep_idt loop_id=goto_program.loop_id(loop);
    out << loop_id << ": ";

    max_boundst::const_iterator it=max_bounds.find(loop);
    if(it!=max_bounds.end())
    {
      int bound=it->second;
      assert(bound>=-1);

      out << bound;
    }
    else
    {
      out << "-"; // unhandled
    }

    out << "\n";
  }
}

void unwind_boundst::output_unwindset(std::ostream &out) const
{
  bool had_one=false;

  for(loop_sett::const_iterator l_it=all_loops.begin();
      l_it!=all_loops.end(); l_it++)
  {
    const locationt loop=*l_it;
    const goto_programt &goto_program=get_goto_program(loop);

    max_boundst::const_iterator it=max_bounds.find(loop);
    if(it!=max_bounds.end())
    {
      int bound=it->second;
      assert(bound>=-1);
      if(bound!=-1)
      {
        irep_idt loop_id=goto_program.loop_id(loop);

        if(had_one)
          out << ", ";

        had_one=true;

        out << loop_id << ": ";
        out << bound;
      }

    }
  }

  out << "\n";
}

void unwind_boundst::output_state_map(
  std::ostream &out,
  const state_mapt &state_map) const
{
  out << "State map size: " << state_map.size() << "\n";

  for(state_mapt::const_iterator it=state_map.begin();
      it!=state_map.end(); it++)
  {
    const locationt l=it->first;
    const constant_propagator_domaint &cpd=it->second;

    out << "Location number: " << l->location_number << "\n";
    out << "State:\n";
    cpd.output(out, dummy, ns);
  }
}

void unwind_boundst::output_inner_loop_map(std::ostream &out) const
{
  out << "Inner loop map:\n";
  for(inner_loop_mapt::const_iterator it=inner_loop_map.begin();
      it!=inner_loop_map.end(); it++)
  {
    const loop_listt &loop_list=it->second;
    const locationt loop=it->first;

    out << loop->location_number << "->\n";

    for(loop_listt::const_iterator i_it=loop_list.begin();
        i_it!=loop_list.end(); i_it++)
    {
      const locationt inner_loop=*i_it;
      out << "  " << inner_loop->location_number << "\n";
    }
  }
}

void unwind_boundst::output_outer_loops(std::ostream &out) const
{
  out << "Outer loops:\n";
  for(loop_sett::const_iterator it=outer_loops.begin();
      it!=outer_loops.end(); it++)
  {
    const locationt loop=*it;
    assert(loop->is_backwards_goto());

    out << "Location: " << loop->location_number << "\n";

    const goto_programt &goto_program=get_goto_program(loop);
    const irep_idt id=goto_program.loop_id(loop);

    out << "Loop id: " << id << "\n";
  }
}

void unwind_boundst::fixpoint_loop(
  const locationt loop,
  const constant_propagator_domaint &entry_state,
  state_mapt &state_map)
{
  assert(state_map.empty());

#ifdef DEBUG_VERBOSE
  std::cout << "========\n";
  std::cout << "Fixpoint loop entry state:\n";
  entry_state.output(std::cout, dummy, ns);
#endif

  const locationt loop_head=get_loop_head(loop);

  constant_propagator_domaint cpd=entry_state; // copy

  location_sett working_set;
  assert(working_set.empty());

  locationt src;
  locationt tgt;

  if(cond_at_head(loop))
  {
    // state at loop head
    state_map[loop_head]=entry_state; // copy
    assert(state_map.size()==1);

    src=loop_head;

    locationt next=loop_head;
    next++;
    tgt=next;
  }
  else
  {
    src=loop;
    tgt=loop_head;
  }

  // pass through loop condition
  cpd.transform(src, tgt, dummy, ns);
  constant_propagator_domaint &target_state=state_map[tgt]; // create
  target_state.merge(cpd, src, tgt);

  assert(state_map.size()==1 || state_map.size()==2);
  fixpoint_loop_body(loop, tgt, state_map);
  assert(!state_map.empty());

#ifdef DEBUG_VERBOSE
  output_state_map(std::cout, state_map);
  std::cout << "<<<<<<<<\n";
#endif
}

void unwind_boundst::fixpoint_loop_body(
  const locationt loop,
  const locationt body,
  state_mapt &state_map)
{
  assert(state_map.size()==1 || state_map.size()==2);
  assert(state_map.find(body)!=state_map.end());

#ifdef DEBUG_VERBOSE
  std::cout << "========\n";
  std::cout << "Fixpoint loop body entry state:\n";
  entry_state.output(std::cout, dummy, ns);
#endif

  const goto_programt &goto_program=get_goto_program(loop);

  const locationt exit=get_loop_exit(loop);

  location_sett working_set;
  assert(working_set.empty());
  working_set.insert(body);

  // do fixpoint
  while(!working_set.empty())
  {
    // get next element from working set
    location_sett::iterator it;
    it=working_set.begin();
    const locationt l=*it;
    working_set.erase(it);

    // starting state
    const constant_propagator_domaint &current_state=state_map[l];

    std::list<locationt> successors=goto_program.get_successors(l);

    assert(successors.size()<=2);
    assert(!l->is_goto() || (!l->guard.is_true() || successors.size()==1));

    for(std::list<locationt>::const_iterator s_it=successors.begin();
        s_it!=successors.end(); s_it++)
    {
      const locationt to_l=*s_it;

      // ignore break edges (breaks in the goto program can result in
      // conditional gotos for code like "if (y) break"), and edges
      // resulting from return statements in the loop body
      if(to_l->location_number>=exit->location_number)
      {
        continue;
      }

      constant_propagator_domaint new_state=current_state; // copy

      if(!l->is_function_call())
      {
        new_state.transform(l, to_l, dummy, ns);
      }
      else
      {
        // calls are not resolved in the goto program
        assert(successors.size()==1);

        if(function_call_handling==UNDER)
        {
          // ignore
        }
        else if(function_call_handling==NO_BODY)
        {
          new_state.transform(l, to_l, dummy, ns);
        }
        else
        {
          assert(function_call_handling==FULL);

          // get called function
          const code_function_callt &code=to_code_function_call(l->code);
          const exprt &call=code.function();

          if(call.id()==ID_symbol)
          {
            const symbol_exprt &symbol_expr=to_symbol_expr(call);
            const irep_idt id=symbol_expr.get_identifier();

            goto_functionst::function_mapt::const_iterator it=
              goto_functions.function_map.find(id);

            if(it!=goto_functions.function_map.end())
            {
              const goto_functiont &goto_function=it->second;
              const goto_programt &called_goto_program=goto_function.body;

              assert(!called_goto_program.empty());
              const locationt l_entry=called_goto_program.instructions.begin();

              // do entry edge
              new_state.transform(l, l_entry, dummy, ns);

              // handle fully
              constant_propagator_ait cp(goto_functions);

              cp.initialize(goto_functions);
              cp.state_map[l_entry]=new_state;

              cp.ai_baset::fixedpoint(called_goto_program, goto_functions, ns);

              const locationt l_end=--called_goto_program.instructions.end();
              new_state=cp.state_map[l_end];
            }
            else
            {
              // handle like no body function
              new_state.transform(l, to_l, dummy, ns);
            }
          }
          else
          {
            // handle like no body function
            new_state.transform(l, to_l, dummy, ns);
          }
        }
      }

      constant_propagator_domaint &target_state=state_map[to_l];
      bool changed;
      changed=target_state.merge(new_state, l, to_l);

      // the backedge is not inserted into the worklist
      if(to_l!=loop && changed)
        working_set.insert(to_l);
    }
  }

  assert(!state_map.empty());

#ifdef DEBUG_VERBOSE
  output_state_map(std::cout, state_map);
  std::cout << "<<<<<<<<\n";
#endif
}

bool unwind_boundst::check_shape(const locationt loop) const
{
  if(!loop->is_backwards_goto())
    return false;

  const locationt loop_head=get_loop_head(loop);

  if(loop_head==loop) // self loops are allowed
    return true;

  locationt next=loop_head;
  next++;

  const locationt loop_exit=get_loop_exit(loop);

#if 0
  // this might happen for loops with a return in their body (goto to
  // END_FUNCTION), and inlined loops that had a return in their body
  // (jump to location after the inlined part)
  //
  // no jump out of the loop beyond the exit
  for(instructionst::const_iterator i_it=next;
      i_it!=loop; i_it++)
  {
    if(!i_it->is_goto())
      continue;

    const locationt target=i_it->get_target();

    if(target->location_number<loop_head->location_number ||
       loop_exit->location_number<target->location_number)
      return false;
  }
#endif

  const goto_programt &goto_program=get_goto_program(loop);

  // no forward jump into the loop (except loop head)
  for(instructionst::const_iterator i_it=goto_program.instructions.begin();
      i_it!=loop_head; i_it++)
  {
    if(!i_it->is_goto())
      continue;

    const locationt target=i_it->get_target();

    if(target->location_number>loop_head->location_number &&
       target->location_number<=loop->location_number)
      return false;
  }

#if 0
  // the inner and outer loop might have the same loop head
  //
  // no backward jump into the loop
  for(instructionst::const_iterator i_it=loop_exit;
      i_it!=goto_program.instructions.end(); i_it++)
  {
    if(!i_it->is_backwards_goto())
      continue;

    const locationt target=i_it->get_target();

    if(target->location_number<=loop->location_number &&
       target->location_number>=loop_head->location_number)
      return false;
  }
#endif

#if 1
  // no backward jump into the loop
  for(instructionst::const_iterator i_it=loop_exit;
      i_it!=goto_program.instructions.end(); i_it++)
  {
    if(!i_it->is_backwards_goto())
      continue;

    const locationt target=i_it->get_target();

    if(target->location_number<=loop->location_number &&
       target->location_number>loop_head->location_number)
      return false;
  }
#endif

  return true;
}

void unwind_boundst::handle_inner_loops(
  const locationt loop,
  const state_mapt &state_map)
{
  const goto_programt &goto_program=get_goto_program(loop);

  assert(state_map.find(loop)!=state_map.end());
  const std::list<locationt> &inner_loops=inner_loop_map[loop];

  for(std::list<locationt>::const_iterator l_it=inner_loops.begin();
      l_it!=inner_loops.end(); l_it++)
  {
    const locationt inner_loop=*l_it;

    if(!check_shape(inner_loop))
    {
#ifdef DEBUG
      assert(false);
#endif
      update_bound(inner_loop, -2);
      continue;
    }

    const locationt inner_loop_head=get_loop_head(inner_loop);

    // starting state for inner loop
    constant_propagator_domaint cpd;
    cpd.make_bottom();
    bool changed=false;

    if(inner_loop_head==goto_program.instructions.begin())
    {
      cpd.make_top();
      changed=true;
    }
    else
    {
      const std::set<goto_programt::targett> &incoming_edges
        =inner_loop_head->incoming_edges;
      assert(!incoming_edges.empty());

      for(std::set<goto_programt::targett>::const_iterator it
            =incoming_edges.begin();
          it!=incoming_edges.end(); it++)
      {
        const locationt l=*it;

        if(l==inner_loop)
          continue;

        constant_propagator_domaint tmp_cpd;
        state_mapt::const_iterator s_it=state_map.find(l);

        if(s_it==state_map.end())
        {
          tmp_cpd.make_top();
        }
        else
        {
          tmp_cpd=s_it->second;
        }

        tmp_cpd.transform(l, inner_loop_head, dummy, ns);
        changed|=cpd.merge(tmp_cpd, l, inner_loop_head);
      }
    }

    if(changed)
    {
      if(is_self_loop(inner_loop))
        handle_self_loop(inner_loop, cpd);
      else
        handle_loop(inner_loop, cpd);
    }
    else
      update_bound(inner_loop, 0);
  }
}

void unwind_boundst::handle_self_loop(
  const locationt loop,
  const constant_propagator_domaint &entry_state)
{
  max_boundst::const_iterator l_it=max_bounds.find(loop);
  if(l_it!=max_bounds.end())
  {
    int max=l_it->second;
    assert(max!=-2);
    if(max==-1)
      return; // we already exceeded the threshold
  }

  // we assume that self loops by definition make a non-conditional
  // iteration

  exprt cond=loop->guard;

  entry_state.values.replace_const.replace(cond);
  cond=simplify_expr(cond, ns);

  bool c=cond.is_false();

  if(c)
    update_bound(loop, 1);
  else
    update_bound(loop, -1);
}

void unwind_boundst::handle_loop(
  const locationt loop,
  const constant_propagator_domaint &entry_state)
{
  assert(loop->is_backwards_goto());
  assert(num_targets(loop)==1);

  max_boundst::const_iterator l_it=max_bounds.find(loop);
  if(l_it!=max_bounds.end())
  {
    int max=l_it->second;
    assert(max!=-2);
    if(max==-1)
      return; // we already exceeded the threshold
  }

  int &execution_counter=loop_executions[loop];
  int loop_counter=0;

  const locationt loop_head=get_loop_head(loop);

  // entry state of next iteration
  constant_propagator_domaint next_entry_state=entry_state; // copy

  state_mapt state_map;
  assert(state_map.empty());

  // first unconditional iteration
  if(!cond_at_head(loop))
  {
    const locationt body=loop_head;
    state_map[body]=next_entry_state;
    assert(state_map.size()==1);

    fixpoint_loop_body(loop, body, state_map);

    // unconditional jump (e.g. break) out of the loop or infinite
    // inner loop; we ignore the inner loops in such cases
    if(state_map.find(loop)==state_map.end())
    {
      update_bound(loop, 1);
      return;
    }

    assert(state_map.find(loop)!=state_map.end());
    next_entry_state=state_map.at(loop);

    loop_counter++;
    execution_counter++;

    if(loop_counter>threshold || execution_counter>threshold_loop)
    {
      update_bound(loop, -1);

      std::list<locationt> inner_loops;
      gather_inner_loops(loop, inner_loops);

      for(std::list<locationt>::const_iterator it=inner_loops.begin();
          it!=inner_loops.end(); it++)
        update_bound(*it, -1);

      return;
    }

    // recursively handle inner loops
    if(dependent_loops)
    {
      handle_inner_loops(loop, state_map);
    }
  }

  while(true)
  {
    exprt cond=loop_cond(loop);
    next_entry_state.values.replace_const.replace(cond);
    cond=simplify_expr(cond, ns);

    bool c=cond.is_false();

    // handle condition
    if(c)
    {
      update_bound(loop, loop_counter);
      return;
    }

    assert(!c);
    loop_counter++;
    execution_counter++;

    if(loop_counter>threshold || execution_counter>threshold_loop)
    {
      update_bound(loop, -1);

      std::list<locationt> inner_loops;
      gather_inner_loops(loop, inner_loops);

      for(std::list<locationt>::const_iterator it=inner_loops.begin();
          it!=inner_loops.end(); it++)
        update_bound(*it, -1);

      return;
    }

    state_map.clear();
    fixpoint_loop(loop, next_entry_state, state_map);

    if(state_map.find(loop)==state_map.end())
    {
      assert(loop_counter==1);
      update_bound(loop, 1);
      return;
    }

    assert(state_map.find(loop)!=state_map.end());
    next_entry_state=state_map.at(loop);

    // recursively handle inner loops
    if(dependent_loops)
    {
      handle_inner_loops(loop, state_map);
    }
  }
}

void unwind_boundst::compute_inner_loops(
  const locationt loop, // outer loop
  const locationt loop_head) // outer loop head
{
  assert(loop->is_backwards_goto());
  assert(loop_head->location_number<loop->location_number);

  reverse_locationt start=forward_to_backward(loop);
  start++; // start one past the outer loop backward edge

  reverse_locationt stop=forward_to_backward(loop_head);
  stop++;

  for(reverse_locationt r_it=start; r_it!=stop; r_it++)
  {
    const locationt i_it=backward_to_forward(r_it);

    // potential inner loop
    if(i_it->is_backwards_goto())
    {
      const locationt inner_loop_head=get_loop_head(i_it);

      // contained
      if(loop_head->location_number<=inner_loop_head->location_number)
      {
        if(i_it!=inner_loop_head)
        {
          compute_inner_loops(i_it, inner_loop_head);
        }

        inner_loop_map[loop].push_front(i_it);
        outer_loops.erase(i_it);

        // continue past the inner loop head
        r_it=forward_to_backward(inner_loop_head);
      }
      else
      {
        assert(i_it!=inner_loop_head);
        compute_inner_loops(i_it, inner_loop_head);
      }
    }
  }
}

void unwind_boundst::update_loop_map(const goto_programt &goto_program)
{
  assert(!goto_program.instructions.empty());

  for(reverse_locationt r_it=goto_program.instructions.crbegin();
      r_it!=goto_program.instructions.crend();
      r_it++)
  {
    const locationt i_it=backward_to_forward(r_it);

    if(i_it->is_backwards_goto())
    {
      const locationt loop_head=get_loop_head(i_it);
      assert(loop_head->location_number<=i_it->location_number);

      if(i_it!=loop_head)
      {
        compute_inner_loops(i_it, loop_head);

        // continue past loop head
        r_it=forward_to_backward(loop_head);
      }
    }
  }
}

void unwind_boundst::compute_loops()
{
  forall_goto_functions(f_it, goto_functions)
  {
    const goto_functiont &goto_function=f_it->second;

    if(!goto_function.body_available())
      continue;

    const goto_programt &goto_program=goto_function.body;

    forall_goto_program_instructions(i_it, goto_program)
    {
      if(i_it->is_backwards_goto())
      {
        all_loops.insert(i_it);
        outer_loops.insert(i_it); // we filter later
      }
    }

    // update loop info for this function
    update_loop_map(goto_program);
  }
}

void unwind_boundst::check_program() const
{
  forall_goto_functions(f_it, goto_functions)
  {
    const goto_functiont &goto_function=f_it->second;

    if(!goto_function.body_available())
      continue;

    const goto_programt &goto_program=goto_function.body;

    forall_goto_program_instructions(i_it, goto_program)
    {
      if(i_it->is_backwards_goto())
      {
        assert(i_it->is_goto());
      }

      if(i_it->is_goto())
      {
        assert(i_it->targets.size()==1);
      }
      else
      {
        assert(i_it->targets.size()==0);
      }
    }
  }
}

void unwind_boundst::operator()()
{
#ifdef DEBUG
  check_program();
#endif

  // get syntactical loops
  compute_loops();

#ifdef DEBUG
  output_outer_loops(std::cout);
  output_inner_loop_map(std::cout);
#endif

  // compute entry states for loops
  constant_propagator_ait cp(goto_functions);
  cp(goto_functions, ns);

#ifdef DEBUG
  goto_functions.output(ns, std::cout);
  cp.output(ns, goto_functions, std::cout);
#endif

  const loop_sett &loops=dependent_loops?outer_loops:all_loops;

  // handle loops
  for(loop_sett::const_iterator l_it=loops.begin();
      l_it!=loops.end(); l_it++)
  {
    const locationt loop=*l_it;
    assert(loop->is_backwards_goto());

    if(!check_shape(loop))
    {
#ifdef DEBUG
      assert(false);
#endif
      update_bound(loop, -2);

      // we don't explore inner loops if outer loop is not
      // well-formed
      continue;
    }

    const goto_programt &goto_program=get_goto_program(loop);

    const locationt loop_head=get_loop_head(loop);

    constant_propagator_domaint cpd;
    cpd.make_bottom();
    bool changed=false;

    if(loop_head==goto_program.instructions.begin())
    {
      // use top
      cpd.make_top();
      changed=true;
    }
    else
    {
      // we use as the starting state the merge result of all
      // edges entering the loop head, except the backedge of
      // this loop

      const std::set<goto_programt::targett> &incoming_edges
        =loop_head->incoming_edges;
      assert(!incoming_edges.empty());

      for(std::set<goto_programt::targett>::const_iterator it
            =incoming_edges.begin();
          it!=incoming_edges.end(); it++)
      {
        const locationt l=*it;

        if(l==loop)
          continue;

        constant_propagator_domaint tmp_cpd=cp[l];
        tmp_cpd.transform(l, loop_head, dummy, ns);
        changed|=cpd.merge(tmp_cpd, l, loop_head);
      }
    }

#ifdef DEBUG
    std::cout << "Entry state:\n";
    cpd.output(std::cout, dummy, ns);
#endif

    if(changed)
    {
      if(is_self_loop(loop))
        handle_self_loop(loop, cpd);
      else
        handle_loop(loop, cpd);
    }
    else
      update_bound(loop, 0); // loop not reachable
  }

  // remove -2 entries (for unhandled loops)
  for(max_boundst::iterator it=max_bounds.begin();
      it!=max_bounds.end();)
  {
    int bound=it->second;
    if(bound==-2)
      it=max_bounds.erase(it);
    else
      it++;
  }
}
