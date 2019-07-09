/*******************************************************************\

Module: Statement List Language Interface

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Interface

#include "statement_list_language.h"
#include "converters/expr2statement_list.h"
#include "statement_list_entry_point.h"
#include "statement_list_parse_tree_io.h"
#include "statement_list_parser.h"
#include "statement_list_typecheck.h"

#include <linking/linking.h>
#include <linking/remove_internal_symbols.h>
#include <util/get_base_name.h>

void statement_list_languaget::set_language_options(const optionst &options)
{
  params = object_factory_parameterst{options};
}

bool statement_list_languaget::generate_support_functions(
  symbol_tablet &symbol_table)
{
  return statement_list_entry_point(symbol_table, get_message_handler());
}

bool statement_list_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module,
  const bool keep_file_local)
{
  symbol_tablet new_symbol_table;

  if(statement_list_typecheck(
       parse_tree, new_symbol_table, module, get_message_handler()))
    return true;

  remove_internal_symbols(
    new_symbol_table, get_message_handler(), keep_file_local);

  if(linking(symbol_table, new_symbol_table, get_message_handler()))
    return true;

  return false;
}

bool statement_list_languaget::parse(
  std::istream &instream,
  const std::string &path)
{
  statement_list_parser.clear();
  parse_path = path;
  statement_list_parser.set_line_no(0);
  statement_list_parser.set_file(path);
  statement_list_parser.in = &instream;
  statement_list_scanner_init();
  bool result = statement_list_parser.parse();

  // store result
  statement_list_parser.swap_tree(parse_tree);

  return result;
}

void statement_list_languaget::show_parse(std::ostream &out)
{
  output_parse_tree(out, parse_tree);
}

bool statement_list_languaget::can_keep_file_local()
{
  return true;
}

bool statement_list_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module)
{
  return typecheck(symbol_table, module, true);
}

bool statement_list_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code = expr2stl(expr, ns);
  return false;
}

bool statement_list_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code = type2stl(type, ns);
  return false;
}

bool statement_list_languaget::type_to_name(
  const typet &type,
  std::string &name,
  const namespacet &ns)
{
  return from_type(type, name, ns);
}

bool statement_list_languaget::to_expr(
  const std::string &,
  const std::string &,
  exprt &,
  const namespacet &)
{
  return true;
}

statement_list_languaget::statement_list_languaget()
{
}

statement_list_languaget::~statement_list_languaget()
{
  parse_tree.clear();
}

void statement_list_languaget::modules_provided(std::set<std::string> &modules)
{
  modules.insert(get_base_name(parse_path, true));
}

std::set<std::string> statement_list_languaget::extensions() const
{
  return {"awl"};
}

std::unique_ptr<languaget> new_statement_list_language()
{
  return util_make_unique<statement_list_languaget>();
}

std::unique_ptr<languaget> statement_list_languaget::new_language()
{
  return util_make_unique<statement_list_languaget>();
}

std::string statement_list_languaget::id() const
{
  return "Statement List";
}

std::string statement_list_languaget::description() const
{
  return "Statement List Language by Siemens";
}
