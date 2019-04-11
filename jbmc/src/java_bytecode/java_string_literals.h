/*******************************************************************\

Module: Java string literal processing

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_STRING_LITERALS_H
#define CPROVER_JAVA_BYTECODE_JAVA_STRING_LITERALS_H

#include <util/symbol_table.h>
#include <util/std_expr.h>

class java_string_literal_exprt;

/// Creates or gets an existing constant global symbol for a given string
/// literal.
/// \param string_expr: string literal expression to convert
/// \param symbol_table: global symbol table. If not already present, constant
///   global symbols will be added.
/// \param string_refinement_enabled: if true, string refinement's string data
///   structure will also be initialised and added to the symbol table.
/// \return a symbol_expr corresponding to the new or existing literal symbol.
symbol_exprt get_or_create_string_literal_symbol(
  const java_string_literal_exprt &string_expr,
  symbol_table_baset &symbol_table,
  bool string_refinement_enabled);

/// Same as
/// get_or_create_string_literal_symbol(const exprt&, symbol_table_baset&, bool)
/// except it takes an id/string parameter rather than a string literal exprt.
symbol_exprt get_or_create_string_literal_symbol(
  const irep_idt &string_value,
  symbol_table_baset &symbol_table,
  bool string_refinement_enabled);

#endif
