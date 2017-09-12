/*******************************************************************\

Module: String Abstraction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// String Abstraction

#ifndef CPROVER_GOTO_PROGRAMS_STRING_INSTRUMENTATION_H
#define CPROVER_GOTO_PROGRAMS_STRING_INSTRUMENTATION_H

#include "goto_functions.h"

class message_handlert;
class goto_modelt;

void string_instrumentation(
  symbol_tablet &,
  message_handlert &,
  goto_programt &);

void string_instrumentation(
  symbol_tablet &,
  message_handlert &,
  goto_functionst &);

void string_instrumentation(
  goto_modelt &,
  message_handlert &);

exprt is_zero_string(const exprt &what, bool write=false);
exprt zero_string_length(const exprt &what, bool write=false);
exprt buffer_size(const exprt &what);

#endif // CPROVER_GOTO_PROGRAMS_STRING_INSTRUMENTATION_H
