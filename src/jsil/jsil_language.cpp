/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

#include <util/symbol_table.h>
#include <util/get_base_name.h>

#include "expr2jsil.h"
#include "expr2jsil_class.h"
#include "jsil_convert.h"
#include "jsil_entry_point.h"
#include "jsil_internal_additions.h"
#include "jsil_parser.h"
#include "jsil_typecheck.h"

#include "jsil_language.h"

/*******************************************************************\

Function: jsil_languaget::extensions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::set<std::string> jsil_languaget::extensions() const
{
  return { "jsil" };
}

/*******************************************************************\

Function: jsil_languaget::modules_provided

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_languaget::modules_provided(std::set<std::string> &modules)
{
  modules.insert(get_base_name(parse_path, true));
}

/*******************************************************************\

Function: jsil_languaget::interfaces

  Inputs:

 Outputs:

 Purpose: Adding symbols for all procedure declarations

\*******************************************************************/

bool jsil_languaget::interfaces(symbol_tablet &symbol_table)
{
  if(jsil_convert(parse_tree, symbol_table, get_message_handler()))
    return true;

  jsil_internal_additions(symbol_table);
  return false;
}

/*******************************************************************\

Function: jsil_languaget::preprocess

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool jsil_languaget::preprocess(
  std::istream &instream,
  const std::string &path,
  std::ostream &outstream)
{
  // there is no preprocessing!
  return true;
}

/*******************************************************************\

Function: jsil_languaget::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: jsil_languaget::typecheck

  Inputs:

 Outputs:

 Purpose: Converting from parse tree and type checking.

\*******************************************************************/

bool jsil_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module)
{
  if(jsil_typecheck(symbol_table, get_message_handler()))
    return true;

  return false;
}

/*******************************************************************\

Function: jsil_languaget::final

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool jsil_languaget::final(
  symbol_tablet &symbol_table,
  bool generate_start_function)
{
  if(generate_start_function)
  {
    if(jsil_entry_point(
         symbol_table,
         get_message_handler()))
      return true;
  }

  return false;
}

/*******************************************************************\

Function: jsil_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_languaget::show_parse(std::ostream &out)
{
  parse_tree.output(out);
}

/*******************************************************************\

Function: new_jsil_language

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

languaget *new_jsil_language()
{
  return new jsil_languaget;
}

/*******************************************************************\

Function: jsil_languaget::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool jsil_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr2jsil(expr, ns);
  return false;
}

/*******************************************************************\

Function: jsil_languaget::from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool jsil_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type2jsil(type, ns);
  return false;
}

/*******************************************************************\

Function: jsil_languaget::get_pretty_printer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::unique_ptr<pretty_printert>
jsil_languaget::get_pretty_printer(const namespacet &ns)
{
  return std::unique_ptr<pretty_printert>(new expr2jsilt(ns));
}

/*******************************************************************\

Function: jsil_languaget::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: jsil_languaget::~jsil_languaget

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

jsil_languaget::~jsil_languaget()
{
}
