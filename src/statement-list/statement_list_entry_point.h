/*******************************************************************\

Module: Statement List Language Entry Point

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Entry Point

#ifndef CPROVER_STATEMENT_LIST_STATEMENT_LIST_ENTRY_POINT_H
#define CPROVER_STATEMENT_LIST_STATEMENT_LIST_ENTRY_POINT_H

class message_handlert;
class symbol_table_baset;

/// Creates a new entry point for the Statement List language.
/// \param [out] symbol_table: Symbol table of the current TIA program. Gets
///   filled with the symbols that are necessary for a proper entry point.
/// \param message_handler: Handler that is responsible for error messages.
bool statement_list_entry_point(
  symbol_table_baset &symbol_table,
  message_handlert &message_handler);

#endif // CPROVER_STATEMENT_LIST_STATEMENT_LIST_ENTRY_POINT_H
