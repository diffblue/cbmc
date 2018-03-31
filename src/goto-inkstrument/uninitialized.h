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

#include <goto-programs/goto_model.h>

void add_uninitialized_locals_assertions(goto_modelt &);

void show_uninitialized(
  const goto_modelt &,
  std::ostream &out);

#endif // CPROVER_GOTO_INSTRUMENT_UNINITIALIZED_H
