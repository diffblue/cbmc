/*******************************************************************\

Module: Detection for Uninitialized Local Variables

Author: Daniel Kroening

Date: January 2010

\*******************************************************************/

/// \file
/// Detection for Uninitialized Local Variables

#ifndef CPROVER_GOTO_INSTRUMENT_UNINITIALIZED_H
#define CPROVER_GOTO_INSTRUMENT_UNINITIALIZED_H

#include <iosfwd>

class goto_modelt;

void add_uninitialized_locals_assertions(goto_modelt &);

void show_uninitialized(
  const goto_modelt &,
  std::ostream &out);

#define OPT_UNINITIALIZED_CHECK "(uninitialized-check)"

#define HELP_UNINITIALIZED_CHECK                                               \
  " --uninitialized-check        add checks for uninitialized locals "         \
  "(experimental)\n" // NOLINT(whitespace/line_length)

#endif // CPROVER_GOTO_INSTRUMENT_UNINITIALIZED_H
