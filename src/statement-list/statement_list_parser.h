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
  /// Constructor
  explicit statement_list_parsert(message_handlert &message_handler)
    : parsert(message_handler)
  {
    // Simplistic check that we don't attempt to do reentrant parsing as the
    // Bison-generated parser has global state.
    PRECONDITION(++instance_count == 1);
  }

  statement_list_parsert(const statement_list_parsert &) = delete;

  ~statement_list_parsert() override
  {
    --instance_count;
  }

  /// Starts the parsing process and saves the result inside of this instance's
  /// parse tree.
  /// \return False if successful.
  bool parse() override;

  /// Adds a function block to the parse tree by converting the \p block
  /// expression tree.
  /// \param block: Root of a function block expression tree.
  void add_function_block(const exprt &block);

  /// Adds a function to the parse tree by converting the \p function
  /// expression tree.
  /// \param function: Root of a function expression tree.
  void add_function(const exprt &function);

  /// Adds a tag list to the parse tree by converting the \p tag_list
  /// expression tree.
  /// \param tag_list: Root of a tag list expression tree.
  void add_tag_list(const exprt &tag_list);

  /// Prints the parse tree of this instance to the given output stream.
  /// \param out: Stream that should receive the result.
  void print_tree(std::ostream &out) const;

  /// Swaps the contents of the parse tree of this instance with \p other.
  /// \param other: Parse tree which should be used in the swap operation.
  void swap_tree(statement_list_parse_treet &other);

private:
  /// Tree that is being filled by the parsing process.
  statement_list_parse_treet parse_tree;

  static int instance_count;
};

/// Forwards any errors that are encountered during the parse process. This
/// function gets called by the generated files of flex and bison.
/// \param parser: Parser object.
/// \param scanner: Lexer state.
/// \param error: Error message.
/// \return Always 0.
int yystatement_listerror(
  statement_list_parsert &parser,
  void *scanner,
  const std::string &error);

#endif // CPROVER_STATEMENT_LIST_STATEMENT_LIST_PARSER_H
