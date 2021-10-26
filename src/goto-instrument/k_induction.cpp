/*******************************************************************\

Module: k-induction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// k-induction

#include "k_induction.h"

#include <analyses/natural_loops.h>
#include <analyses/local_may_alias.h>

#include <goto-programs/remove_skip.h>

#include "havoc_utils.h"
#include "loop_utils.h"
#include "unwind.h"

class k_inductiont
{
public:
  k_inductiont(
    const irep_idt &_function_id,
    goto_functiont &_goto_function,
    bool _base_case,
    bool _step_case,
    unsigned _k)
    : function_id(_function_id),
      goto_function(_goto_function),
      local_may_alias(_goto_function),
      natural_loops(_goto_function.body),
      base_case(_base_case),
      step_case(_step_case),
      k(_k)
  {
    k_induction();
  }

protected:
  const irep_idt &function_id;
  goto_functiont &goto_function;
  local_may_aliast local_may_alias;
  natural_loops_mutablet natural_loops;

  const bool base_case, step_case;
  const unsigned k;

  void k_induction();

  void process_loop(
    const goto_programt::targett loop_head,
    const loopt &);
};

void k_inductiont::process_loop(
  const goto_programt::targett loop_head,
  const loopt &loop)
{
  assert(!loop.empty());

  // save the loop guard
  const exprt loop_guard=loop_head->guard;

  // compute the loop exit
  goto_programt::targett loop_exit=
    get_loop_exit(loop);

  if(base_case)
  {
    // now unwind k times
    goto_unwindt goto_unwind;
    goto_unwind.unwind(
      function_id,
      goto_function.body,
      loop_head,
      loop_exit,
      k,
      goto_unwindt::unwind_strategyt::PARTIAL);

    // assume the loop condition has become false
    goto_programt::instructiont assume =
      goto_programt::make_assumption(loop_guard);
    goto_function.body.insert_before_swap(loop_exit, assume);
  }

  if(step_case)
  {
    // step case

    // find out what can get changed in the loop
    modifiest modifies;
    get_modifies(local_may_alias, loop, modifies);

    // build the havocking code
    goto_programt havoc_code;
    havoc_utilst havoc_gen(modifies);
    havoc_gen.append_full_havoc_code(loop_head->source_location(), havoc_code);

    // unwind to get k+1 copies
    std::vector<goto_programt::targett> iteration_points;

    goto_unwindt goto_unwind;
    goto_unwind.unwind(
      function_id,
      goto_function.body,
      loop_head,
      loop_exit,
      k + 1,
      goto_unwindt::unwind_strategyt::PARTIAL,
      iteration_points);

    // we can remove everything up to the first assertion
    for(goto_programt::targett t=loop_head; t!=loop_exit; t++)
    {
      if(t->is_assert())
        break;
      t->turn_into_skip();
    }

    // now turn any assertions in iterations 0..k-1 into assumptions
    assert(iteration_points.size()==k+1);

    assert(k>=1);
    goto_programt::targett end=iteration_points[k-1];

    for(goto_programt::targett t=loop_head; t!=end; t++)
    {
      assert(t!=goto_function.body.instructions.end());
      if(t->is_assert())
        t->turn_into_assume();
    }

    // assume the loop condition has become false
    goto_programt::instructiont assume =
      goto_programt::make_assumption(loop_guard);
    goto_function.body.insert_before_swap(loop_exit, assume);

    // Now havoc at the loop head. Use insert_swap to
    // preserve jumps to loop head.
    goto_function.body.insert_before_swap(loop_head, havoc_code);
  }

  // remove skips
  remove_skip(goto_function.body);
}

void k_inductiont::k_induction()
{
  // iterate over the (natural) loops in the function

  for(natural_loops_mutablet::loop_mapt::const_iterator
      l_it=natural_loops.loop_map.begin();
      l_it!=natural_loops.loop_map.end();
      l_it++)
    process_loop(l_it->first, l_it->second);
}

void k_induction(
  goto_modelt &goto_model,
  bool base_case, bool step_case,
  unsigned k)
{
  for(auto &gf_entry : goto_model.goto_functions.function_map)
    k_inductiont(gf_entry.first, gf_entry.second, base_case, step_case, k);
}
