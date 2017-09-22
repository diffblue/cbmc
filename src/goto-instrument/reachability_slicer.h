/*******************************************************************\

Module: Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Slicing

#ifndef CPROVER_GOTO_INSTRUMENT_REACHABILITY_SLICER_H
#define CPROVER_GOTO_INSTRUMENT_REACHABILITY_SLICER_H

#include <list>
#include <string>

class goto_modelt;

void reachability_slicer(goto_modelt &);

void reachability_slicer(
  goto_modelt &,
  const std::list<std::string> &properties);

#endif // CPROVER_GOTO_INSTRUMENT_REACHABILITY_SLICER_H
