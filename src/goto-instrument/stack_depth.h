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
class message_handlert;

/// Add assertions to all user-defined functions in \p goto_model that the call
/// stack depth does not exceed \p depth.
/// Warnings are reported via \p message_handler.
void stack_depth(
  goto_modelt &goto_model,
  const std::size_t depth,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_INSTRUMENT_STACK_DEPTH_H
