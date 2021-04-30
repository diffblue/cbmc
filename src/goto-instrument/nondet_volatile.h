/*******************************************************************\

Module: Volatile Variables

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Volatile Variables

#ifndef CPROVER_GOTO_INSTRUMENT_NONDET_VOLATILE_H
#define CPROVER_GOTO_INSTRUMENT_NONDET_VOLATILE_H

#include <functional>

class cmdlinet;
class exprt;
class goto_modelt;
class optionst;

// clang-format off
#define NONDET_VOLATILE_OPT "nondet-volatile"
#define NONDET_VOLATILE_VARIABLE_OPT "nondet-volatile-variable"
#define NONDET_VOLATILE_MODEL_OPT "nondet-volatile-model"

#define OPT_NONDET_VOLATILE \
  "(" NONDET_VOLATILE_OPT ")" \
  "(" NONDET_VOLATILE_VARIABLE_OPT "):" \
  "(" NONDET_VOLATILE_MODEL_OPT "):"

#define HELP_NONDET_VOLATILE \
  help_entry( \
    "--" NONDET_VOLATILE_OPT, \
    "makes reads from volatile variables non-deterministic") << \
  help_entry( \
    "--" NONDET_VOLATILE_VARIABLE_OPT " <variable>", \
    "makes reads from given volatile variable non-deterministic") << \
  help_entry( \
    "--" NONDET_VOLATILE_MODEL_OPT " <variable>:<model>", \
    "models reads from given volatile variable by a call to the given model")
// clang-format on

void parse_nondet_volatile_options(const cmdlinet &cmdline, optionst &options);

/// Havoc reads from volatile expressions, if enabled in the options
///
/// \param goto_model: the goto model in which to havoc volatile reads
/// \param options: command line options
void nondet_volatile(goto_modelt &goto_model, const optionst &options);

/// Havoc reads from volatile expressions
///
/// \param goto_model: the goto model in which to havoc volatile reads
/// \param should_havoc: predicate indicating if the given volatile expression
///   should be havocked
void nondet_volatile(
  goto_modelt &goto_model,
  std::function<bool(const exprt &)> should_havoc = [](const exprt &) {
    return true;
  });

#endif // CPROVER_GOTO_INSTRUMENT_NONDET_VOLATILE_H
