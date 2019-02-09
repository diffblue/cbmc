/*******************************************************************\

Module: Incremental Bounded Model Checking for ANSI-C

Author: Peter Schrammel, Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <limits>

#include <util/source_location.h>
#include <util/xml.h>

#include "symex_bmc_incremental_one_loop.h"

symex_bmc_incremental_one_loopt::symex_bmc_incremental_one_loopt(
  message_handlert &message_handler,
  const symbol_tablet &outer_symbol_table,
  symex_target_equationt &target,
  const optionst &options,
  path_storaget &path_storage,
  guard_managert &guard_manager)
  : symex_bmct(
      message_handler,
      outer_symbol_table,
      target,
      options,
      path_storage,
      guard_manager),
    incr_loop_id(options.get_option("incremental-loop")),
    incr_max_unwind(
      options.is_set("unwind-max") ? options.get_signed_int_option("unwind-max")
                                   : std::numeric_limits<unsigned>::max()),
    incr_min_unwind(
      options.is_set("unwind-min") ? options.get_signed_int_option("unwind-min")
                                   : 0)
{
}

bool symex_bmc_incremental_one_loopt::should_stop_unwind(
  const symex_targett::sourcet &source,
  const call_stackt &context,
  unsigned unwind)
{
  const irep_idt id = goto_programt::loop_id(source.function_id, *source.pc);

  tvt abort_unwind_decision;
  unsigned this_loop_limit = std::numeric_limits<unsigned>::max();

  // use the incremental limits if it is the specified incremental loop
  if(id == incr_loop_id)
  {
    this_loop_limit = incr_max_unwind;
    if(unwind + 1 >= incr_min_unwind)
      ignore_assertions = false;
    abort_unwind_decision = tvt(unwind >= this_loop_limit);
  }
  else
  {
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
      auto limit = unwindset.get_limit(id, source.thread_nr);

      if(!limit.has_value())
        abort_unwind_decision = tvt(false);
      else
        abort_unwind_decision = tvt(unwind >= *limit);
    }
  }

  INVARIANT(
    abort_unwind_decision.is_known(), "unwind decision should be taken by now");
  bool abort = abort_unwind_decision.is_true();

  log.statistics() << (abort ? "Not unwinding" : "Unwinding") << " loop " << id
                   << " iteration " << unwind;

  if(this_loop_limit != std::numeric_limits<unsigned>::max())
    log.statistics() << " (" << this_loop_limit << " max)";

  log.statistics() << " " << source.pc->source_location << " thread "
                   << source.thread_nr << log.eom;

  return abort;
}

/// Defines condition for interrupting symbolic execution for incremental BMC
/// \return True if the back edge encountered during symbolic execution
///   corresponds to the given loop (incr_loop_id)
bool symex_bmc_incremental_one_loopt::check_break(
  const irep_idt &id,
  bool is_function,
  statet &state,
  const exprt &cond,
  unsigned unwind)
{
  if(unwind < incr_min_unwind)
    return false;

  // loop specified by incremental-loop
  return (id == incr_loop_id);
}

bool symex_bmc_incremental_one_loopt::from_entry_point_of(
  const get_goto_functiont &get_goto_function,
  symbol_tablet &new_symbol_table)
{
  state = initialize_entry_point_state(get_goto_function);

  symex_with_state(*state, get_goto_function, new_symbol_table);

  return should_pause_symex;
}

bool symex_bmc_incremental_one_loopt::resume(
  const get_goto_functiont &get_goto_function)
{
  should_pause_symex = false;

  symex_with_state(*state, get_goto_function, state->symbol_table);

  return should_pause_symex;
}
