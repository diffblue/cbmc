/*******************************************************************\

Module: JSON symbol table deserialization

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_JSON_SYMTAB_LANGUAGE_JSON_SYMBOL_TABLE_H
#define CPROVER_JSON_SYMTAB_LANGUAGE_JSON_SYMBOL_TABLE_H

class jsont;
class symbol_table_baset;

/// Add the symbols of the JSON symbol table \p in to \p symbol_table, and
/// check the structure of all types and expressions in \p symbol_table (see
/// \ref check_symbol_table_structure). Checks that require looking up symbols
/// are left to the caller, see \ref validate_symbols. Throws
/// deserialization_exceptiont or invalid_input_exceptiont on malformed input.
void symbol_table_from_json(const jsont &in, symbol_table_baset &symbol_table);

#endif
