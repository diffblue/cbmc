/*******************************************************************\

Module: Stack depth checks

Author: Daniel Kroening, Michael Tautschnig

Date: November 2011

\*******************************************************************/

/// \file
/// Stack depth checks

#ifndef CPROVER_GOTO_INSTRUMENT_STACK_DEPTH_H
#define CPROVER_GOTO_INSTRUMENT_STACK_DEPTH_H

#include <cstddef>

class goto_modelt;

void stack_depth(
  goto_modelt &,
  const std::size_t depth);

#endif // CPROVER_GOTO_INSTRUMENT_STACK_DEPTH_H
