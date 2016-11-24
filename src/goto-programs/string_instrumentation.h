/*******************************************************************\

Module: String Abstraction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_STRING_INSTRUMENTATION_H
#define CPROVER_GOTO_PROGRAMS_STRING_INSTRUMENTATION_H

#include "goto_functions.h"

void string_instrumentation(
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  goto_programt &dest);

void string_instrumentation(
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  goto_functionst &dest);

exprt is_zero_string(const exprt &what, bool write=false);
exprt zero_string_length(const exprt &what, bool write=false);
exprt buffer_size(const exprt &what);

#endif
