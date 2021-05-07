/*******************************************************************\

Module: Dump Goto-Program as DOT Graph

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Dump Goto-Program as DOT Graph

#ifndef CPROVER_GOTO_INSTRUMENT_DOT_H
#define CPROVER_GOTO_INSTRUMENT_DOT_H

#include <iosfwd>

class goto_modelt;

void dot(
  const goto_modelt &,
  std::ostream &out);

#endif // CPROVER_GOTO_INSTRUMENT_DOT_H
