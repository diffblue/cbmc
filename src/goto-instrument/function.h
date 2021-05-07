/*******************************************************************\

Module: Function Entering and Exiting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Function Entering and Exiting

#ifndef CPROVER_GOTO_INSTRUMENT_FUNCTION_H
#define CPROVER_GOTO_INSTRUMENT_FUNCTION_H

#include <util/irep.h>

class goto_modelt;
class symbol_tablet;

class code_function_callt function_to_call(
  symbol_tablet &,
  const irep_idt &id,
  const irep_idt &argument);

void function_enter(
  goto_modelt &,
  const irep_idt &id);

void function_exit(
  goto_modelt &,
  const irep_idt &id);

#endif // CPROVER_GOTO_INSTRUMENT_FUNCTION_H
