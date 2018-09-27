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

void function_path_reachability_slicer(
  goto_modelt &goto_model,
  const std::string &functions_list);

void reachability_slicer(
  goto_modelt &,
  const bool include_forward_reachability);

void reachability_slicer(
  goto_modelt &,
  const std::list<std::string> &properties,
  const bool include_forward_reachability);

// clang-format off
#define OPT_REACHABILITY_SLICER                                                \
  "(fp-reachability-slice):(reachability-slice)(reachability-slice-fb)" // NOLINT(*)

#define HELP_REACHABILITY_SLICER                                               \
  " --fp-reachability-slice <f>  remove instructions that cannot appear on a " \
  "trace that visits all given functions. The list of functions has to be "    \
  "given as a comma separated list.\n"                                         \
  " --reachability-slice         remove instructions that cannot appear on a " \
  "trace from entry point to a property\n"                                     \
  " --reachability-slice-fb      remove instructions that cannot appear on a " \
  "trace from entry point through a property\n" // NOLINT(*)
// clang-format on
#endif // CPROVER_GOTO_INSTRUMENT_REACHABILITY_SLICER_H
