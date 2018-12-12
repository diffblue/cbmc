/*******************************************************************\

Module: Goto Verifier Interface

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier Interface

#include "goto_verifier.h"

goto_verifiert::goto_verifiert(
  const optionst &_options,
  ui_message_handlert &ui_message_handler)
  : options(_options),
    ui_message_handler(ui_message_handler),
    log(ui_message_handler)
{
}
