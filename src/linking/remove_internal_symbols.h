/*******************************************************************\

Module: Remove symbols that are internal only

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Remove symbols that are internal only

#ifndef CPROVER_LINKING_REMOVE_INTERNAL_SYMBOLS_H
#define CPROVER_LINKING_REMOVE_INTERNAL_SYMBOLS_H

#include <util/message.h>

#include <string>

void remove_internal_symbols(
  class symbol_tablet &symbol_table,
  message_handlert &,
  const bool);

#endif // CPROVER_LINKING_REMOVE_INTERNAL_SYMBOLS_H
