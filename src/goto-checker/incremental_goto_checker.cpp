/*******************************************************************\

Module: Incremental Goto Checker Interface

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Incremental Goto Checker Interface

#include "incremental_goto_checker.h"

incremental_goto_checkert::incremental_goto_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler)
  : options(options),
    ui_message_handler(ui_message_handler),
    log(ui_message_handler)
{
}

incremental_goto_checkert::resultt::resultt(
  progresst progress,
  const std::vector<irep_idt> &updated_properties)
  : progress(progress), updated_properties(updated_properties)
{
}
