/*******************************************************************\

Module: Goto Checker Interface

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker Interface

#include "goto_checker.h"

goto_checkert::goto_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler)
  : messaget(ui_message_handler),
    options(options),
    ui_message_handler(ui_message_handler)
{
}
