/*******************************************************************\

 Module: Incremental Bounded Model Checking for ANSI-C

 Author: Peter Schrammel, Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_CHECKER_SYMEX_BMC_INCREMENTAL_ONE_LOOP_H
#define CPROVER_GOTO_CHECKER_SYMEX_BMC_INCREMENTAL_ONE_LOOP_H

#include "symex_bmc.h"
#include <util/ui_message.h>

class symex_bmc_incremental_one_loopt : public symex_bmct
{
public:
  symex_bmc_incremental_one_loopt(
    message_handlert &,
    const symbol_tablet &outer_symbol_table,
    symex_target_equationt &,
    const optionst &,
    path_storaget &,
    guard_managert &,
    unwindsett &,
    ui_message_handlert::uit output_ui);

  /// Return true if symex can be resumed
  bool from_entry_point_of(
    const get_goto_functiont &get_goto_function,
    symbol_tablet &new_symbol_table);

  /// Return true if symex can be resumed
  bool resume(const get_goto_functiont &get_goto_function);

protected:
  const irep_idt incr_loop_id;
  const unsigned incr_max_unwind;
  const unsigned incr_min_unwind;

  std::unique_ptr<goto_symext::statet> state;

  // returns true if the symbolic execution is to be interrupted for checking
  bool check_break(const irep_idt &loop_id, unsigned unwind) override;

  bool should_stop_unwind(
    const symex_targett::sourcet &source,
    const call_stackt &context,
    unsigned unwind) override;

  void log_unwinding(unsigned unwind);

  ui_message_handlert::uit output_ui;
};

#endif // CPROVER_GOTO_CHECKER_SYMEX_BMC_INCREMENTAL_ONE_LOOP_H
