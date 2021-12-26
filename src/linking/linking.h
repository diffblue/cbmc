/*******************************************************************\

Module: ANSI-C Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Linking

#ifndef CPROVER_LINKING_LINKING_H
#define CPROVER_LINKING_LINKING_H

class message_handlert;
class symbol_tablet;

/// Merges the symbol table \p new_symbol_table into \p dest_symbol_table,
/// renaming symbols from \p new_symbol_table when necessary.
/// \return True, iff linking failed with unresolvable conflicts.
bool linking(
  symbol_tablet &dest_symbol_table,
  const symbol_tablet &new_symbol_table,
  message_handlert &message_handler);

#endif // CPROVER_LINKING_LINKING_H
