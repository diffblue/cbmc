/*******************************************************************\

Module: k-induction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// k-induction

#include "k_induction.h"

#include <util/expr_util.h>
#include <util/std_expr.h>

#include <goto-programs/remove_skip.h>

#include <analyses/local_may_alias.h>
#include <analyses/natural_loops.h>

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
    unsigned _k,
    const namespacet &ns)
    : function_id(_function_id),
      goto_function(_goto_function),
      local_may_alias(_goto_function),
      natural_loops(_goto_function.body),
      base_case(_base_case),
      step_case(_step_case),
      k(_k),
      ns(ns)
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

  const namespacet &ns;

  void k_induction();

  static exprt find_loop_guard(
    goto_programt::targett loop_head,
    goto_programt::targett loop_exit,
    const loopt &loop);

  void process_loop(
    const goto_programt::targett loop_head,
    const loopt &);
};

/// Find the loop *exit* condition, i.e. the condition under which control
/// leaves the loop. This is what process_loop assumes (via make_assumption)
/// right before the loop exit, modelling "the loop condition has become
/// false". For a continue condition `c` this returns `¬c`. The guard can be
/// expressed in one of two ways:
/// 1. as a conditional backwards goto at the end of the loop (the backedge),
///    whose condition is the *continue* condition `c`, so we negate it;
/// 2. as a forward goto at the loop head that targets the loop exit, whose
///    condition is already the *exit* condition `¬c`.
/// If neither is found (e.g. an unconditional/infinite loop with no
/// identifiable guard), we fall back to `true`: as an exit assumption this is
/// permissive (it prunes no states) and hence sound.
exprt k_inductiont::find_loop_guard(
  const goto_programt::targett loop_head,
  const goto_programt::targett loop_exit,
  const loopt &loop)
{
  // Find the backwards goto (backedge) for this loop
  goto_programt::targett backedge;
  bool found_backedge = false;
  for(const auto &t : loop)
  {
    if(t->is_backwards_goto() && t->get_target() == loop_head)
    {
      backedge = t;
      found_backedge = true;
      break;
    }
  }

  // The backedge condition is the loop *continue* condition; the exit
  // condition is its negation.
  if(found_backedge && !backedge->condition().is_true())
    return boolean_negate(backedge->condition());

  // A forward goto at the loop head that jumps to the loop exit already holds
  // the exit condition.
  if(loop_head->is_goto())
  {
    if(loop_head->get_target() == loop_exit)
      return loop_head->condition();
  }

  return true_exprt();
}

void k_inductiont::process_loop(
  const goto_programt::targett loop_head,
  const loopt &loop)
{
  PRECONDITION(!loop.empty());

  // compute the loop exit
  goto_programt::targett loop_exit=
    get_loop_exit(loop);

  const exprt loop_guard = find_loop_guard(loop_head, loop_exit, loop);

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
    assignst assigns;
    get_assigns(local_may_alias, loop, assigns);

    // build the havocking code
    goto_programt havoc_code;
    havoc_utilst havoc_gen(assigns, ns);
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
    DATA_INVARIANT(
      iteration_points.size() == k + 1, "number of iteration points");

    DATA_INVARIANT(k >= 1, "at least one iteration");
    goto_programt::targett end=iteration_points[k-1];

    for(goto_programt::targett t=loop_head; t!=end; t++)
    {
      DATA_INVARIANT(
        t != goto_function.body.instructions.end(), "t is in range");
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
}

void k_inductiont::k_induction()
{
  // Iterate over the (natural) loops in the function and process the outermost
  // loops only; inner loops are handled as part of the outer loop body during
  // unwinding.
  //
  // Processing a loop inserts instructions (which does not invalidate
  // std::list iterators) but must not erase any, or it would invalidate the
  // goto_programt::targett iterators held as keys/values in
  // natural_loops.loop_map that we keep iterating here. At k >= 1 the unwinder
  // only inserts; the sole erasing step is remove_skip, which we therefore
  // defer to a single call once the whole map has been processed (see below).

  for(const auto &[loop_head, loop] : natural_loops.loop_map)
  {
    bool is_nested = false;

    for(const auto &[other_head, other_loop] : natural_loops.loop_map)
    {
      if(other_head != loop_head && other_loop.contains(loop_head))
      {
        is_nested = true;
        break;
      }
    }

    if(!is_nested)
      process_loop(loop_head, loop);
  }

  // Now that we no longer iterate loop_map, it is safe to erase the skip
  // instructions introduced during processing.
  remove_skip(goto_function.body);
}

void k_induction(
  goto_modelt &goto_model,
  bool base_case, bool step_case,
  unsigned k)
{
  for(auto &gf_entry : goto_model.goto_functions.function_map)
  {
    k_inductiont(
      gf_entry.first,
      gf_entry.second,
      base_case,
      step_case,
      k,
      namespacet{goto_model.symbol_table});
  }
}
