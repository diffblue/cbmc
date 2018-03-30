/*******************************************************************\

Module: ANSI-C Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Linking

#ifndef CPROVER_LINKING_LINKING_H
#define CPROVER_LINKING_LINKING_H

#include <util/message.h>
#include <util/symbol_table.h>

// This merges the symbol table "new_symbol_table" into "dest_symbol_table",
// applying appropriate renamings to symbols in "new_symbol_table"
// when necessary.

bool inking(
  symbol_tablet &dest_symbol_table,
  symbol_tablet &new_symbol_table,
  message_handlert &message_handler);

#endif // CPROVER_LINKING_LINKING_H
