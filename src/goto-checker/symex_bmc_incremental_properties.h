/*******************************************************************\

 Module: Incremental Bounded Model Checking for ANSI-C

 Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_GOTO_CHECKER_SYMEX_BMC_INCREMENTAL_PROPERTIES_H
#define CPROVER_GOTO_CHECKER_SYMEX_BMC_INCREMENTAL_PROPERTIES_H

#include <util/ui_message.h>

#include "symex_bmc.h"

class symex_bmc_incremental_propertiest : public symex_bmct
{
public:
  symex_bmc_incremental_propertiest(
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
  void symex_assert(const goto_programt::instructiont &, statet &) override;

  std::unique_ptr<goto_symext::statet> state;

  ui_message_handlert::uit output_ui;
};

#endif // CPROVER_GOTO_CHECKER_SYMEX_BMC_INCREMENTAL_PROPERTIES_H
