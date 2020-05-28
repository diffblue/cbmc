/*******************************************************************\

Module: Volatile Variables

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Volatile Variables

#ifndef CPROVER_GOTO_INSTRUMENT_NONDET_VOLATILE_H
#define CPROVER_GOTO_INSTRUMENT_NONDET_VOLATILE_H

#include <goto-programs/goto_model.h>

class cmdlinet;
class optionst;

// clang-format off
#define NONDET_VOLATILE_OPT "nondet-volatile"
#define NONDET_VOLATILE_VARIABLE_OPT "nondet-volatile-variable"

#define OPT_NONDET_VOLATILE \
  "(" NONDET_VOLATILE_OPT ")" \
  "(" NONDET_VOLATILE_VARIABLE_OPT "):"

#define HELP_NONDET_VOLATILE \
  " --" NONDET_VOLATILE_OPT "        makes reads from volatile variables " \
  "non-deterministic\n" \
  " --" NONDET_VOLATILE_VARIABLE_OPT " <variable>\n" \
  "                              makes reads from given volatile variable " \
  "non-deterministic\n"
// clang-format on

void parse_nondet_volatile_options(const cmdlinet &cmdline, optionst &options);
void nondet_volatile(goto_modelt &goto_model, const optionst &options);

void nondet_volatile(
  goto_modelt &goto_model,
  std::function<bool(const exprt &)> = [](const exprt &) { return true; });

#endif // CPROVER_GOTO_INSTRUMENT_NONDET_VOLATILE_H
