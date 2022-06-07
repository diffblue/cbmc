/*******************************************************************\

Module: Incremental Bounded Model Checking for ANSI-C

Author: Michael Tautschnig

\*******************************************************************/

#include "symex_bmc_incremental_properties.h"

#include <util/structured_data.h>

#include <goto-instrument/unwindset.h>

#include <limits>

symex_bmc_incremental_propertiest::symex_bmc_incremental_propertiest(
  message_handlert &message_handler,
  const symbol_tablet &outer_symbol_table,
  symex_target_equationt &target,
  const optionst &options,
  path_storaget &path_storage,
  guard_managert &guard_manager,
  unwindsett &unwindset,
  ui_message_handlert::uit output_ui)
  : symex_bmct(
      message_handler,
      outer_symbol_table,
      target,
      options,
      path_storage,
      guard_manager,
      unwindset),
    output_ui(output_ui)
{
}

bool symex_bmc_incremental_propertiest::from_entry_point_of(
  const get_goto_functiont &get_goto_function,
  symbol_tablet &new_symbol_table)
{
  state = initialize_entry_point_state(get_goto_function);

  symex_with_state(*state, get_goto_function, new_symbol_table);

  return should_pause_symex;
}

bool symex_bmc_incremental_propertiest::resume(
  const get_goto_functiont &get_goto_function)
{
  should_pause_symex = false;

  symex_with_state(*state, get_goto_function, state->symbol_table);

  return should_pause_symex;
}

void symex_bmc_incremental_propertiest::symex_assert(
  const goto_programt::instructiont &instruction,
  statet &goto_state)
{
  symex_bmct::symex_assert(instruction, goto_state);
  should_pause_symex = true;
}
