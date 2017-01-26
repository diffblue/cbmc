/*******************************************************************\

Module: Compute unwind bounds

Author: Daniel Poetzl

\*******************************************************************/

/// \file
/// Compute unwind bounds

#ifndef CPROVER_UNWIND_BOUNDS_H
#define CPROVER_UNWIND_BOUNDS_H

#include <iosfwd>

#include <goto-programs/goto_model.h>
#include <analyses/constant_propagator.h>
#include <util/simplify_expr.h>

class unwind_boundst
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;
  typedef goto_programt::instructiont instructiont;
  typedef goto_programt::instructionst instructionst;
  typedef goto_programt::const_targett locationt;
  typedef instructionst::const_reverse_iterator reverse_locationt;

  typedef std::map<locationt, constant_propagator_domaint> state_mapt;
  typedef std::list<locationt> loop_listt;
  typedef std::set<locationt> loop_sett;
  typedef std::set<locationt> location_sett;

  // strategy for handling function calls:
  // - underapproximate (i.e., ignore)
  // - treat all functions as a black box but soundly (i.e., as if the
  //   body were not available)
  // - handle function calls fully
  typedef enum { UNDER, NO_BODY, FULL } function_call_handlingt;

  unwind_boundst(
    const goto_modelt &goto_model,
    const bool dependent_loops=true,
    const unsigned threshold=100,
    const unsigned threshold_loop=100000,
    const function_call_handlingt function_call_handling=NO_BODY) :
      unwind_boundst(
        goto_model.goto_functions,
        goto_model.symbol_table,
        dependent_loops,
        threshold,
        threshold_loop,
        function_call_handling)
  {

  }

  unwind_boundst(
    const goto_functionst &goto_functions,
    const symbol_tablet &symbol_table,
    const bool dependent_loops=true,
    const unsigned threshold=100,
    const unsigned threshold_loop=100000,
    const function_call_handlingt function_call_handling=NO_BODY) :
      goto_functions(goto_functions),
      symbol_table(symbol_table),
      ns(symbol_table),
      dependent_loops(dependent_loops),
      threshold(threshold),
      threshold_loop(threshold_loop),
      function_call_handling(function_call_handling),
      dummy(goto_functions)
  {
    assert(threshold>0);
    assert(threshold_loop>0);
  }

  void clear()
  {
    max_bounds.clear();
    inner_loop_map.clear();
    all_loops.clear();
    outer_loops.clear();
  }

  void operator()();
  void output(std::ostream &out) const;
  void output_unwindset(std::ostream &out) const;

  // maximum bound for loop found so far:
  // >= 0:     loop bound
  // -1:       bound exceeded threshold
  // no entry: loop not handled
  typedef std::map<locationt, int> max_boundst;
  max_boundst max_bounds;

protected:

  void output_state_map(std::ostream &out, const state_mapt &state_map) const;
  void output_inner_loop_map(std::ostream &out) const;
  void output_outer_loops(std::ostream &out) const;

  locationt get_loop_exit(const locationt loop) const
  {
    assert(loop->is_backwards_goto());

    locationt loop_exit=loop;
    loop_exit++;
    return loop_exit;
  }

  locationt get_loop_head(const locationt l) const
  {
    assert(l->is_backwards_goto());
    assert(num_targets(l)==1);

    locationt target=l->get_target();

    return target;
  }

  void fixpoint_loop(
    const locationt loop,
    const constant_propagator_domaint &entry_state,
    state_mapt &state_map);

  void fixpoint_loop_body(
    const locationt loop,
    const locationt body,
    state_mapt &state_map);

  // loop condition is either at the head or the backedge
  bool cond_at_head(const locationt loop) const
  {
    assert(loop->is_backwards_goto());

    const exprt &guard=loop->guard;

    const locationt loop_head=get_loop_head(loop);
    const locationt loop_exit=get_loop_exit(loop);

    bool b=true;

    b&=guard.is_true();
    b&=loop_head->is_goto() && loop_head->get_target()==loop_exit;

    return b;
  }

  // loop continuation condition
  exprt loop_cond(const locationt loop) const
  {
    exprt cond;

    if(cond_at_head(loop))
    {
      const locationt loop_head=get_loop_head(loop);
      assert(loop_head->is_goto());

      cond=loop_head->guard;
      cond.make_not();
    }
    else
    {
      cond=loop->guard;
    }

    return cond;
  }

  bool is_self_loop(const locationt loop) const
  {
    assert(loop->is_backwards_goto());

    return get_loop_head(loop)==loop;
  }

  int num_targets(const locationt l) const
  {
    return l->targets.size();
  }

  // -2:  unhandled
  // -1:  exceeded some threshold
  // >=0: bound
  void update_bound(const locationt loop, int bound)
  {
    assert(bound>=-2);

    max_boundst::const_iterator b_it=max_bounds.find(loop);
    if(b_it!=max_bounds.end())
    {
      int max=b_it->second; // current

      if((bound<0 && bound<max) ||
         (bound>=0 && max>=0 && bound>max))
      {
        max_bounds[loop]=bound;
      }
    }
    else
    {
      max_bounds[loop]=bound;
    }
  }

  void gather_inner_loops(
    const locationt loop,
    std::list<locationt> &inner_loops) const
  {
    assert(loop->is_backwards_goto());
    assert(inner_loops.empty());

    std::list<locationt> worklist;
    worklist.push_back(loop);

    do
    {
      const locationt next=worklist.front();
      worklist.pop_front();

      inner_loop_mapt::const_iterator it=inner_loop_map.find(next);
      if(it!=inner_loop_map.end())
      {
        const std::list<locationt> &l=it->second;

        inner_loops.insert(inner_loops.end(), l.begin(), l.end());
        worklist.insert(worklist.end(), l.begin(), l.end());
      }
    } while(!worklist.empty());
  }

  bool check_shape(const locationt loop) const;

  // for debugging
  void check_program() const;

  void handle_loop(
    const locationt loop,
    const constant_propagator_domaint &entry_state);

  void handle_self_loop(
    const locationt loop,
    const constant_propagator_domaint &entry_state);

  void handle_inner_loops(
    const locationt loop,
    const state_mapt &state_map);

  void compute_inner_loops(
    const locationt loop,
    const locationt loop_head);

  void update_loop_map(const goto_programt &goto_program);

  void compute_loops();

  const goto_programt &get_goto_program(const locationt l) const
  {
    locationt i_it=l;

    while(!i_it->is_end_function())
      i_it++;

    irep_idt id=i_it->function;
    assert(!id.empty());

    const goto_functiont &goto_function=goto_functions.function_map.at(id);
    assert(goto_function.body_available());
    const goto_programt &goto_program=goto_function.body;

    locationt e_it=goto_program.instructions.end();
    e_it--;
    assert(e_it->is_end_function());

    assert(i_it==e_it);

    return goto_program;
  }

  locationt backward_to_forward(reverse_locationt l) const
  {
    locationt it=l.base();
    it--; // move one backwards in sequence
    return it;
  }

  reverse_locationt forward_to_backward(locationt l) const
  {
    reverse_locationt it(l);
    it--; // move one forward in sequence
    return it;
  }

  const goto_functionst &goto_functions;
  const symbol_tablet &symbol_table;
  const namespacet ns;

  // analyze inner loops for each iteration of the outer loop
  const bool dependent_loops;

  // we report -1 as the bound for loops for which a threshold was
  // exceeded during abstract execution
  const int threshold; // execution bound per loop instance
  const int threshold_loop; // execution bound per loop

  const function_call_handlingt function_call_handling;

  typedef std::map<locationt, int> loop_executionst;
  loop_executionst loop_executions;

  // the transformers need this
  constant_propagator_ait dummy;

  // mapping from outer to inner loops (no entry or empty list means
  // there are no inner loops)
  typedef std::map<locationt, loop_listt> inner_loop_mapt;
  inner_loop_mapt inner_loop_map;

  // all loops in the program
  loop_sett all_loops;

  // loops that are not inner loops of other loops
  loop_sett outer_loops;
};

#endif
