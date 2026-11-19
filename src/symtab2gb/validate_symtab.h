/*******************************************************************\

Module: Validation of symbol tables and goto functions read from JSON

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Validation of symbol tables and goto functions read from JSON

#ifndef CPROVER_SYMTAB2GB_VALIDATE_SYMTAB_H
#define CPROVER_SYMTAB2GB_VALIDATE_SYMTAB_H

// The functions below visit every type and expression, knowing for each
// position whether it holds a type or an expression. Each node is checked with
// the check (and, given a namespace, validate) function that
// util/validate_expressions.cpp and util/validate_types.cpp dispatch to for its
// id, or the check of one of the expressions declared in ansi-c/c_expr.h. Ids
// that neither covers are not checked beyond their operands and types.

class goto_functionst;
class namespacet;
class symbol_tablet;

/// Check the structure (e.g., the number of operands) of every type and
/// expression in \p symbol_table, without consulting a namespace. This is
/// meant to be used before linking, which can then rely on well-formed
/// input. Throws invalid_input_exceptiont naming the offending symbol.
/// \param symbol_table: the symbol table read from a single input file
void check_symbol_table_structure(const symbol_tablet &symbol_table);

/// Validate every type and expression in \p symbol_table, including checks
/// that require a namespace (e.g., that struct tags are defined). Throws
/// invalid_input_exceptiont naming the offending symbol.
/// \param symbol_table: the (linked) symbol table
/// \param symbol_names_prefix: only validate symbols whose name has this
///   prefix
void validate_symbol_table(
  const symbol_tablet &symbol_table,
  const char *symbol_names_prefix = "");

/// Validate every type and expression in the instructions of
/// \p goto_functions against \p ns. Throws invalid_input_exceptiont naming
/// the offending function.
/// \param goto_functions: goto functions read from JSON
/// \param ns: namespace of the linked symbol table
void validate_goto_functions(
  const goto_functionst &goto_functions,
  const namespacet &ns);

#endif // CPROVER_SYMTAB2GB_VALIDATE_SYMTAB_H
