/*******************************************************************\

Module: Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_REACHABILITY_SLICER_H
#define CPROVER_GOTO_INSTRUMENT_REACHABILITY_SLICER_H

#include <goto-programs/goto_functions.h>

void reachability_slicer(goto_functionst &goto_functions);

void reachability_slicer(
  goto_functionst &goto_functions,
  const std::list<std::string> &properties);

#endif // CPROVER_GOTO_INSTRUMENT_REACHABILITY_SLICER_H
