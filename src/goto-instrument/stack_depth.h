/*******************************************************************\

Module: Stack depth checks

Author: Daniel Kroening, Michael Tautschnig

Date: November 2011

\*******************************************************************/

/// \file
/// Stack depth checks

#ifndef CPROVER_GOTO_INSTRUMENT_STACK_DEPTH_H
#define CPROVER_GOTO_INSTRUMENT_STACK_DEPTH_H

class goto_modelt;

void stack_depth(
  goto_modelt &,
  const int depth);

#endif // CPROVER_GOTO_INSTRUMENT_STACK_DEPTH_H
