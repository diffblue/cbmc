/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_CONVERT_H
#define CPROVER_GOTO_PROGRAMS_GOTO_CONVERT_H

#include <message.h>
#include <std_code.h>

#include "goto_program.h"

// start from given code
void goto_convert(
  const codet &code,
  symbol_tablet &symbol_table,
  goto_programt &dest,
  message_handlert &message_handler);

// start from "main"
void goto_convert(
  symbol_tablet &symbol_table,
  goto_programt &dest,
  message_handlert &message_handler);

#endif
