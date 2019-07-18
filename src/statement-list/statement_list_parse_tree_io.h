/*******************************************************************\

Module: Statement List Language Parse Tree Output

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Parse Tree Output

#ifndef CPROVER_STATEMENT_LIST_STATEMENT_LIST_PARSE_TREE_IO_H
#define CPROVER_STATEMENT_LIST_STATEMENT_LIST_PARSE_TREE_IO_H

#include "statement_list_parse_tree.h"

/// Prints the given Statement List parse tree in a human-readable form to the
/// given output stream.
/// \param os: Stream that should receive the result.
/// \param tree: Parse Tree whose contents should be printed.
void output_parse_tree(
  std::ostream &os,
  const statement_list_parse_treet &tree);

/// Prints the given Statement List function block in a human-readable form to
/// the given output stream.
/// \param os: Stream that should receive the result.
/// \param block: Function block whose contents should be printed.
void output_function_block(
  std::ostream &os,
  const statement_list_parse_treet::function_blockt &block);

/// Prints the given Statement List function in a human-readable form to
/// the given output stream.
/// \param os: Stream that should receive the result.
/// \param function: Function whose contents should be printed.
void output_function(
  std::ostream &os,
  const statement_list_parse_treet::functiont &function);

/// Prints the basic information about a TIA module to the given output stream.
/// \param module: TIA module whose contents should be printed.
/// \param os: Stream that should receive the result.
void output_tia_module_properties(
  const statement_list_parse_treet::tia_modulet &module,
  std::ostream &os);

/// Prints the return value of a function to the given output stream.
/// \param function: Function whose return value should be printed.
/// \param os: Stream that should receive the result.
void output_return_value(
  const statement_list_parse_treet::functiont &function,
  std::ostream &os);

/// Prints all variable declarations functions and function blocks have in
/// common to the given output stream.
/// \param os: Stream that should receive the result.
/// \param module: TIA module whose variable declarations should be printed.
void output_common_var_declarations(
  std::ostream &os,
  const statement_list_parse_treet::tia_modulet &module);

/// Prints the static variable declarations of a function block to the given
/// output stream.
/// \param os: Stream that should receive the result.
/// \param block: Function block whose static variables should be
///   printed.
void output_static_var_declarations(
  std::ostream &os,
  const statement_list_parse_treet::function_blockt &block);

/// Prints all variable declarations of the given list to the given output
/// stream.
/// \param os: Stream that should receive the result.
/// \param declarations: List whose contents should be printed.
void output_var_declaration_list(
  std::ostream &os,
  const statement_list_parse_treet::var_declarationst &declarations);

/// Prints the given Statement List variable declaration in a human-readable
/// form to the given output stream.
/// \param os: Stream that should receive the result.
/// \param declaration: Declaration that should be printed.
void output_var_declaration(
  std::ostream &os,
  const statement_list_parse_treet::var_declarationt &declaration);

/// Prints the given network list in a human-readable form to the given output
/// stream.
/// \param os: Stream that should receive the result.
/// \param networks: List whose contents should be printed.
void output_network_list(
  std::ostream &os,
  const statement_list_parse_treet::networkst &networks);

/// Prints the given Statement List network in a human-readable form to the
/// given output stream.
/// \param os: Stream that should receive the result.
/// \param network: Network that should be printed.
void output_network(
  std::ostream &os,
  const statement_list_parse_treet::networkt &network);

/// Prints the given Statement List instruction in a human-readable form to the
/// given output stream.
/// \param os: Stream that should receive the result.
/// \param instruction: Instruction that should be printed.
void output_instruction(
  std::ostream &os,
  const statement_list_parse_treet::instructiont &instruction);

#endif // CPROVER_STATEMENT_LIST_STATEMENT_LIST_PARSE_TREE_IO_H
