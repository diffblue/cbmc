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

void reachability_slicer(
  goto_modelt &,
  const bool include_forward_reachability);

void reachability_slicer(
  goto_modelt &,
  const std::list<std::string> &properties,
  const bool include_forward_reachability);

#define OPT_REACHABILITY_SLICER                                                \
  "(reachability-slice)(reachability-slice-fb)" // NOLINT(*)

#define HELP_REACHABILITY_SLICER                                               \
  " --reachability-slice         remove instructions that cannot appear on a " \
  "trace from entry point to a property\n"                                     \
  " --reachability-slice-fb      remove instructions that cannot appear on a " \
  "trace from entry point through a property\n" // NOLINT(*)

#endif // CPROVER_GOTO_INSTRUMENT_REACHABILITY_SLICER_H
