/*******************************************************************\

Module: Statement List Language Parser

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Parser

#ifndef CPROVER_STATEMENT_LIST_STATEMENT_LIST_PARSER_H
#define CPROVER_STATEMENT_LIST_STATEMENT_LIST_PARSER_H

#include <util/parser.h>

#include "statement_list_parse_tree.h"

// Defined in statement_list_y.tab.cpp.
int yystatement_listparse();

/// Responsible for starting the parse process and to translate the result into
/// a statement_list_parse_treet. This parser works by using the expression
/// stack of its base class. During the parse process, expressions with
/// different IDs and types are put on this stack and may get associated with
/// each other. This way a tree structure with expressions as nodes is created.
/// If the parser encounters a function or function block, it invokes
/// add_function() or add_function_block(). These functions then convert the
/// expression tree structure into a statement_list_parse_treet::functiont or
/// statement_list_parse_treet::function_blockt and add it to the
/// statement_list_parse_treet. See the implementation of scanner.l and
/// parser.y for details about how and when the stack operations are performed.
class statement_list_parsert : public parsert
{
public:
  /// Starts the parsing process and saves the result inside of this instance's
  /// parse tree.
  /// \return: False if successful.
  bool parse() override
  {
    return yystatement_listparse() != 0;
  }

  /// Adds a function block to the parse tree by converting the \p block
  /// expression tree.
  void add_function_block(exprt &block);

  /// Adds a function to the parse tree by converting the \p function
  /// expression tree.
  void add_function(exprt &function);

  /// Prints the parse tree of this instance to the given output stream.
  void print_tree(std::ostream &out) const;

  /// Swaps the contents of the parse tree of this instance with \p other.
  void swap_tree(statement_list_parse_treet &other);

  /// Removes all functions and function blocks from the parse tree and
  /// clears the internal state of the parser.
  void clear() override;

private:
  statement_list_parse_treet parse_tree;

  /// Searches for the name of the function element inside of its root
  /// expression.
  /// \param root: Expression that includes the element's name as a
  ///   direct operand.
  /// \return The name of the function element.
  static irep_idt find_name(const exprt &root);

  /// Searches for the version of the function element inside of its root
  /// expression.
  /// \param root: Expression that includes the element's version as a
  ///   direct operand.
  /// \return The version of the function element.
  static float find_version(const exprt &root);

  /// Searches for the variable list of the function element inside of its root
  /// expression.
  /// \param root: Expression that includes the element's variable list as a
  ///   direct operand.
  /// \return The variable list of the function element.
  static exprt find_variable_list(const exprt &root);

  /// Adds all valid variable declarations to the given function element.
  /// \param function: The function to which the variables belong.
  /// \param var_decls: The root expression of a valid variable list.
  static void find_variables(
    statement_list_parse_treet::functiont &function,
    const exprt &var_decls);

  /// Adds all input variable declarations to the given function element.
  /// \param function: The function to which the variables belong.
  /// \param input_vars: The root expression of a input variable list.
  static void fill_input_vars(
    statement_list_parse_treet::functiont &function,
    const exprt &input_vars);

  /// Adds all input variable declarations to the given function element.
  /// \param function: The function to which the variables belong.
  /// \param inout_vars: The root expression of a inout variable list.
  static void fill_inout_vars(
    statement_list_parse_treet::functiont &function,
    const exprt &inout_vars);

  /// Adds all input variable declarations to the given function element.
  /// \param function: The function to which the variables belong.
  /// \param output_vars: The root expression of a output variable list.
  static void fill_output_vars(
    statement_list_parse_treet::functiont &function,
    const exprt &output_vars);

  /// Searches for the network list of the function element inside of its root
  /// expression.
  /// \param root: Expression that includes the element's network list as a
  ///   direct operand.
  /// \return The network list of the function element.
  static exprt find_network_list(const exprt &root);

  /// Adds all valid networks and their instructions to the given function
  /// element.
  /// \param function: The function to which the networks belong.
  /// \param network_list: The root expression of a valid network list.
  static void find_networks(
    statement_list_parse_treet::functiont &function,
    const exprt &network_list);

  /// Searches for the title of a network inside of its root expression.
  /// \param network: Expression that includes the network's title as a
  ///   direct operand.
  /// \return The title of the network.
  static std::string find_network_title(const exprt &network);

  /// Searches for the instruction list of a network inside of its root
  /// expression.
  /// \param network: Expression that includes the network's instructions as a
  ///   direct operand.
  /// \return The instruction list expression of the network.
  static exprt find_network_instructions(const exprt &network);

  /// Adds all valid  instructions to the given network.
  /// \param network: The network to which the instructions belong.
  /// \param instructions: The root expression of a valid instruction list.
  static void find_instructions(
    statement_list_parse_treet::networkt &network,
    const exprt &instructions);
};

extern statement_list_parsert statement_list_parser;

/// Forwards any errors that are encountered during the parse process. This
/// function gets called by the generated files of flex and bison.
/// \param error: Error message.
/// \return Always 0.
int yystatement_listerror(const std::string &error);
void statement_list_scanner_init();

#endif // CPROVER_STATEMENT_LIST_STATEMENT_LIST_PARSER_H
