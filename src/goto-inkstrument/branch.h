/*******************************************************************\

Module: Branch Instrumentation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Branch Instrumentation

#ifndef CPROVER_GOTO_INSTRUMENT_BRANCH_H
#define CPROVER_GOTO_INSTRUMENT_BRANCH_H

#include <util/irep.h>

class goto_modelt;

void branch(
  goto_modelt &,
  const irep_idt &id);

#endif // CPROVER_GOTO_INSTRUMENT_BRANCH_H
