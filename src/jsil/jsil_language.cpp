/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#include "jsil_language.h"

#include <util/symbol_table.h>
#include <util/get_base_name.h>

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
bool jsil_languaget::interfaces(symbol_tablet &symbol_table)
{
  if(jsil_convert(parse_tree, symbol_table, get_message_handler()))
    return true;

  jsil_internal_additions(symbol_table);
  return false;
}

/// Generate a _start function for a specific function
/// \param entry_function_symbol_id: The symbol for the function that should be
///   used as the entry point
/// \param symbol_table: The symbol table for the program. The new _start
///   function symbol will be added to this table
/// \return Returns false if the _start method was generated correctly
bool jsil_languaget::generate_start_function(
  const irep_idt &entry_function_symbol_id,
  symbol_tablet &symbol_table)
{
  // TODO(tkiley): This should be implemented if this language
  // is used.
  UNREACHABLE;
  return true;
}

bool jsil_languaget::preprocess(
  std::istream &instream,
  const std::string &path,
  std::ostream &outstream)
{
  // there is no preprocessing!
  return true;
}

bool jsil_languaget::parse(
  std::istream &instream,
  const std::string &path)
{
  // store the path
  parse_path=path;

  // parsing
  jsil_parser.clear();
  jsil_parser.set_file(path);
  jsil_parser.in=&instream;
  jsil_parser.set_message_handler(get_message_handler());

  jsil_scanner_init();
  bool result=jsil_parser.parse();

  // save result
  parse_tree.swap(jsil_parser.parse_tree);

  // save some memory
  jsil_parser.clear();

  return result;
}

/// Converting from parse tree and type checking.
bool jsil_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module)
{
  if(jsil_typecheck(symbol_table, get_message_handler()))
    return true;

  return false;
}

bool jsil_languaget::final(symbol_tablet &symbol_table)
{
  if(jsil_entry_point(
      symbol_table,
      get_message_handler()))
    return true;

  return false;
}

void jsil_languaget::show_parse(std::ostream &out)
{
  parse_tree.output(out);
}

std::unique_ptr<languaget> new_jsil_language()
{
  return util_make_unique<jsil_languaget>();
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
  const std::string &module,
  exprt &expr,
  const namespacet &ns)
{
  expr.make_nil();
  std::istringstream instream(code);

  // parsing

  jsil_parser.clear();
  jsil_parser.set_file("");
  jsil_parser.in=&instream;
  jsil_parser.set_message_handler(get_message_handler());
  jsil_scanner_init();

  bool result=jsil_parser.parse();

  if(jsil_parser.parse_tree.items.size()!=1)
    result=true;
  else
  {
    symbol_tablet symbol_table;
    result=
      jsil_convert(parse_tree, symbol_table, get_message_handler());

    if(symbol_table.symbols.size()!=1)
      result=true;

    if(!result)
      expr=symbol_table.symbols.begin()->second.value;

    // typecheck it
    if(!result)
      result=jsil_typecheck(expr, get_message_handler(), ns);
  }

  // save some memory
  jsil_parser.clear();

  return result;
}

jsil_languaget::~jsil_languaget()
{
}
