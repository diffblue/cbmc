/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_CONVERT_H
#define CPROVER_GOTO_PROGRAMS_GOTO_CONVERT_H

#include <util/irep.h>

class codet;
class goto_programt;
class message_handlert;
class symbol_table_baset;

// start from given code
void goto_convert(
  const codet &code,
  symbol_table_baset &symbol_table,
  goto_programt &dest,
  message_handlert &message_handler,
  const irep_idt &mode);

// start from "main"
void goto_convert(
  symbol_table_baset &symbol_table,
  goto_programt &dest,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_PROGRAMS_GOTO_CONVERT_H
