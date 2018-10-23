/*******************************************************************\

Module: Bounded Model Checking for ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Bounded Model Checking for ANSI-C

#include "symex_bmc.h"

#include <goto-symex/symex_target_equation.h>

#include <limits>

#include <util/source_location.h>
#include <util/simplify_expr.h>

symex_bmct::symex_bmct(
  message_handlert &mh,
  const symbol_tablet &outer_symbol_table,
  symex_target_equationt &_target,
  const optionst &options,
  path_storaget &path_storage)
  : goto_symext(mh, outer_symbol_table, _target, options, path_storage),
    record_coverage(!options.get_option("symex-coverage-report").empty()),
    symex_coverage(ns)
{
}

/// show progress
void symex_bmct::symex_step(
  const get_goto_functiont &get_goto_function,
  statet &state)
{
  const source_locationt &source_location=state.source.pc->source_location;

  if(!source_location.is_nil() && last_source_location!=source_location)
  {
    log.debug() << "BMC at " << source_location.as_string()
                << " (depth " << state.depth << ')' << log.eom;

    last_source_location=source_location;
  }

  const goto_programt::const_targett cur_pc=state.source.pc;
  const guardt cur_guard=state.guard;

  if(!state.guard.is_false() &&
     state.source.pc->is_assume() &&
     simplify_expr(state.source.pc->guard, ns).is_false())
  {
    log.statistics() << "aborting path on assume(false) at "
                     << state.source.pc->source_location << " thread "
                     << state.source.thread_nr;

    const irep_idt &c=state.source.pc->source_location.get_comment();
    if(!c.empty())
      log.statistics() << ": " << c;

    log.statistics() << log.eom;
  }

  goto_symext::symex_step(get_goto_function, state);

  if(record_coverage &&
     // avoid an invalid iterator in state.source.pc
     (!cur_pc->is_end_function() ||
      cur_pc->function!=goto_functionst::entry_point()))
  {
    // forward goto will effectively be covered via phi function,
    // which does not invoke symex_step; as symex_step is called
    // before merge_gotos, also state.guard will be false (we have
    // taken an impossible transition); thus we synthesize a
    // transition from the goto instruction to its target to make
    // sure the goto is considered covered
    if(cur_pc->is_goto() &&
       cur_pc->get_target()!=state.source.pc &&
       cur_pc->guard.is_true())
      symex_coverage.covered(cur_pc, cur_pc->get_target());
    else if(!state.guard.is_false())
      symex_coverage.covered(cur_pc, state.source.pc);
  }
}

void symex_bmct::merge_goto(
  const statet::goto_statet &goto_state,
  statet &state)
{
  const goto_programt::const_targett prev_pc=goto_state.source.pc;
  const guardt prev_guard=goto_state.guard;

  goto_symext::merge_goto(goto_state, state);

  PRECONDITION(prev_pc->is_goto());
  if(record_coverage &&
     // could the branch possibly be taken?
     !prev_guard.is_false() &&
     !state.guard.is_false() &&
     // branches only, no single-successor goto
     !prev_pc->guard.is_true())
    symex_coverage.covered(prev_pc, state.source.pc);
}

bool symex_bmct::get_unwind(
  const symex_targett::sourcet &source,
  const goto_symex_statet::call_stackt &context,
  unsigned unwind)
{
  const irep_idt id=goto_programt::loop_id(*source.pc);

  tvt abort_unwind_decision;
  unsigned this_loop_limit=std::numeric_limits<unsigned>::max();

  for(auto handler : loop_unwind_handlers)
  {
    abort_unwind_decision =
      handler(context, source.pc->loop_number, unwind, this_loop_limit);
    if(abort_unwind_decision.is_known())
      break;
  }

  // If no handler gave an opinion, use standard command-line --unwindset
  // / --unwind options to decide:
  if(abort_unwind_decision.is_unknown())
  {
    auto limit=unwindset.get_limit(id, source.thread_nr);

    if(!limit.has_value())
      abort_unwind_decision = tvt(false);
    else
      abort_unwind_decision = tvt(unwind >= *limit);
  }

  INVARIANT(
    abort_unwind_decision.is_known(), "unwind decision should be taken by now");
  bool abort = abort_unwind_decision.is_true();

  log.statistics() << (abort ? "Not unwinding" : "Unwinding") << " loop " << id
                   << " iteration " << unwind;

  if(this_loop_limit!=std::numeric_limits<unsigned>::max())
    log.statistics() << " (" << this_loop_limit << " max)";

  log.statistics() << " " << source.pc->source_location << " thread "
                   << source.thread_nr << log.eom;

  return abort;
}

bool symex_bmct::get_unwind_recursion(
  const irep_idt &id,
  const unsigned thread_nr,
  unsigned unwind)
{
  tvt abort_unwind_decision;
  unsigned this_loop_limit=std::numeric_limits<unsigned>::max();

  for(auto handler : recursion_unwind_handlers)
  {
    abort_unwind_decision = handler(id, unwind, this_loop_limit);
    if(abort_unwind_decision.is_known())
      break;
  }

  // If no handler gave an opinion, use standard command-line --unwindset
  // / --unwind options to decide:
  if(abort_unwind_decision.is_unknown())
  {
    auto limit=unwindset.get_limit(id, thread_nr);

    if(!limit.has_value())
      abort_unwind_decision = tvt(false);
    else
      abort_unwind_decision = tvt(unwind > *limit);
  }

  INVARIANT(
    abort_unwind_decision.is_known(), "unwind decision should be taken by now");
  bool abort = abort_unwind_decision.is_true();

  if(unwind>0 || abort)
  {
    const symbolt &symbol=ns.lookup(id);

    log.statistics() << (abort ? "Not unwinding" : "Unwinding") << " recursion "
                     << symbol.display_name() << " iteration " << unwind;

    if(this_loop_limit!=std::numeric_limits<unsigned>::max())
      log.statistics() << " (" << this_loop_limit << " max)";

    log.statistics() << log.eom;
  }

  return abort;
}

void symex_bmct::no_body(const irep_idt &identifier)
{
  if(body_warnings.insert(identifier).second)
  {
    log.warning() << "**** WARNING: no body for function " << identifier
                  << log.eom;
  }
}
