/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#include "jsil_language.h"

#include <util/get_base_name.h>
#include <util/symbol_table.h>

#include "expr2jsil.h"
#include "jsil_convert.h"
#include "jsil_entry_point.h"
#include "jsil_internal_additions.h"
#include "jsil_parser.h"
#include "jsil_typecheck.h"

std::set<std::string> jsil_languaget::extensions() const
{
  return { "jsil" };
}

void jsil_languaget::modules_provided(std::set<std::string> &modules)
{
  modules.insert(get_base_name(parse_path, true));
}

/// Adding symbols for all procedure declarations
bool jsil_languaget::interfaces(
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  if(jsil_convert(parse_tree, symbol_table, message_handler))
    return true;

  jsil_internal_additions(symbol_table);
  return false;
}

bool jsil_languaget::preprocess(
  std::istream &,
  const std::string &,
  std::ostream &,
  message_handlert &)
{
  // there is no preprocessing!
  return true;
}

bool jsil_languaget::parse(
  std::istream &instream,
  const std::string &path,
  message_handlert &message_handler)
{
  // store the path
  parse_path=path;

  // parsing
  jsil_parsert jsil_parser{message_handler};
  jsil_parser.clear();
  jsil_parser.set_file(path);
  jsil_parser.in=&instream;

  bool result=jsil_parser.parse();

  // save result
  parse_tree.swap(jsil_parser.parse_tree);

  // save some memory
  jsil_parser.clear();

  return result;
}

/// Converting from parse tree and type checking.
bool jsil_languaget::typecheck(
  symbol_table_baset &symbol_table,
  const std::string &,
  message_handlert &message_handler)
{
  if(jsil_typecheck(symbol_table, message_handler))
    return true;

  return false;
}

bool jsil_languaget::generate_support_functions(
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  return jsil_entry_point(symbol_table, message_handler);
}

void jsil_languaget::show_parse(std::ostream &out, message_handlert &)
{
  parse_tree.output(out);
}

std::unique_ptr<languaget> new_jsil_language()
{
  return std::make_unique<jsil_languaget>();
}

bool jsil_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr2jsil(expr, ns);
  return false;
}

bool jsil_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type2jsil(type, ns);
  return false;
}

bool jsil_languaget::to_expr(
  const std::string &code,
  const std::string &,
  exprt &expr,
  const namespacet &ns,
  message_handlert &message_handler)
{
  expr.make_nil();
  std::istringstream instream(code);

  // parsing
  jsil_parsert jsil_parser{message_handler};
  jsil_parser.clear();
  jsil_parser.set_file(irep_idt());
  jsil_parser.in=&instream;

  bool result=jsil_parser.parse();

  if(jsil_parser.parse_tree.items.size()!=1)
    result=true;
  else
  {
    symbol_tablet symbol_table;
    result = jsil_convert(parse_tree, symbol_table, message_handler);

    if(symbol_table.symbols.size()!=1)
      result=true;

    if(!result)
      expr=symbol_table.symbols.begin()->second.value;

    // typecheck it
    if(!result)
      result = jsil_typecheck(expr, message_handler, ns);
  }

  // save some memory
  jsil_parser.clear();

  return result;
}

jsil_languaget::~jsil_languaget()
{
}
