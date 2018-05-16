/*******************************************************************\

Module: Java string literal processing

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_STRING_LITERALS_H
#define CPROVER_JAVA_BYTECODE_JAVA_STRING_LITERALS_H

#include <util/symbol_table.h>
#include <util/std_expr.h>

symbol_exprt get_or_create_string_literal_symbol(
  const exprt &string_expr,
  symbol_table_baset &symbol_table,
  bool string_refinement_enabled);

#endif
