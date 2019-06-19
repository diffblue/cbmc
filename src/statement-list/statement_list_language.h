/*******************************************************************\

Module: Statement List Language Interface

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Interface

#ifndef CPROVER_STATEMENT_LIST_STATEMENT_LIST_LANGUAGE_H
#define CPROVER_STATEMENT_LIST_STATEMENT_LIST_LANGUAGE_H

#include "statement_list_parse_tree.h"
#include <langapi/language.h>
#include <util/make_unique.h>
#include <util/object_factory_parameters.h>

/// Implements the language interface for the Statement List language.
/// Includes functions for parsing input streams and for converting the
/// resulting parse tree into a symbol table.
class statement_list_languaget : public languaget
{
public:
  /// Sets language specific options.
  /// \param options: Options that shall apply during the parse and
  ///   typecheck process.
  void set_language_options(const optionst &options) override;

  /// Parses input given by \p instream and saves this result to this
  /// instance's parse tree.
  /// \param instream: Input to parse.
  /// \param path: Path of the input.
  /// \return: False if successful.
  bool parse(std::istream &instream, const std::string &path) override;

  /// Currently unused.
  bool generate_support_functions(symbol_tablet &symbol_table) override;

  /// Converts the current parse tree into a symbol table.
  /// \param [out] symbol_table: Object that shall be filled by this function.
  ///   If the symbol table is not empty when calling this function, its
  ///   contents are merged with the new entries.
  /// \param module: Name of the file that has been parsed.
  /// \param keep_file_local: Set to true if local variables of this module
  ///   should be included in the table.
  /// \return: False if no errors occurred, true otherwise.
  bool typecheck(
    symbol_tablet &symbol_table,
    const std::string &module,
    const bool keep_file_local) override;

  bool
  typecheck(symbol_tablet &symbol_table, const std::string &module) override;

  bool can_keep_file_local() override;

  /// Prints the parse tree to the given output stream.
  void show_parse(std::ostream &out) override;

  // Constructor and destructor.
  ~statement_list_languaget() override;
  statement_list_languaget();

  /// Formats the given expression in a language-specific way.
  /// \param expr: the expression to format
  /// \param code: the formatted expression
  /// \param ns: a namespace
  /// \return false if conversion succeeds
  bool from_expr(const exprt &expr, std::string &code, const namespacet &ns)
    override;

  /// Formats the given type in a language-specific way.
  /// \param type: the type to format
  /// \param code: the formatted type
  /// \param ns: a namespace
  /// \return false if conversion succeeds
  bool from_type(const typet &type, std::string &code, const namespacet &ns)
    override;

  /// Encodes the given type in a language-specific way.
  /// \param type: the type to encode
  /// \param name: the encoded type
  /// \param ns: a namespace
  /// \return false if the conversion succeeds
  bool type_to_name(const typet &type, std::string &name, const namespacet &ns)
    override;

  /// Parses the given string into an expression.
  /// \param code: the string to parse
  /// \param module: prefix to be used for identifiers
  /// \param expr: the parsed expression
  /// \param ns: a namespace
  /// \return false if the conversion succeeds
  bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    const namespacet &ns) override;

  std::unique_ptr<languaget> new_language() override;

  // ID, description, extensions, modules.
  std::string id() const override;
  std::string description() const override;
  std::set<std::string> extensions() const override;
  void modules_provided(std::set<std::string> &modules) override;

private:
  statement_list_parse_treet parse_tree;
  std::string parse_path;
  object_factory_parameterst params;
};

std::unique_ptr<languaget> new_statement_list_language();

#endif // CPROVER_STATEMENT_LIST_STATEMENT_LIST_LANGUAGE_H
