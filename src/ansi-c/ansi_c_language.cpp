/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstring>
#include <sstream>
#include <fstream>

#include <util/config.h>
#include <util/get_base_name.h>

#include <linking/linking.h>
#include <linking/remove_internal_symbols.h>

#include "ansi_c_entry_point.h"
#include "ansi_c_language.h"
#include "ansi_c_typecheck.h"
#include "ansi_c_parser.h"
#include "expr2c.h"
#include "expr2c_class.h"
#include "c_preprocess.h"
#include "ansi_c_internal_additions.h"
#include "type2name.h"

/*******************************************************************\

Function: ansi_c_languaget::extensions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::set<std::string> ansi_c_languaget::extensions() const
{
  return { "c", "i" };
}

/*******************************************************************\

Function: ansi_c_languaget::modules_provided

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_languaget::modules_provided(std::set<std::string> &modules)
{
  modules.insert(get_base_name(parse_path, true));
}

/*******************************************************************\

Function: ansi_c_languaget::preprocess

  Inputs:

 Outputs:

 Purpose: ANSI-C preprocessing

\*******************************************************************/

bool ansi_c_languaget::preprocess(
  std::istream &instream,
  const std::string &path,
  std::ostream &outstream)
{
  // stdin?
  if(path=="")
    return c_preprocess(instream, outstream, get_message_handler());

  return c_preprocess(path, outstream, get_message_handler());
}

/*******************************************************************\

Function: ansi_c_languaget::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ansi_c_languaget::parse(
  std::istream &instream,
  const std::string &path)
{
  // store the path
  parse_path=path;

  // preprocessing
  std::ostringstream o_preprocessed;

  if(preprocess(instream, path, o_preprocessed))
    return true;

  std::istringstream i_preprocessed(o_preprocessed.str());

  // parsing

  std::string code;
  ansi_c_internal_additions(code);
  std::istringstream codestr(code);

  ansi_c_parser.clear();
  ansi_c_parser.set_file(ID_built_in);
  ansi_c_parser.in=&codestr;
  ansi_c_parser.set_message_handler(get_message_handler());
  ansi_c_parser.for_has_scope=config.ansi_c.for_has_scope;
  ansi_c_parser.cpp98=false; // it's not C++
  ansi_c_parser.cpp11=false; // it's not C++
  ansi_c_parser.mode=config.ansi_c.mode;

  ansi_c_scanner_init();

  bool result=ansi_c_parser.parse();

  if(!result)
  {
    ansi_c_parser.set_line_no(0);
    ansi_c_parser.set_file(path);
    ansi_c_parser.in=&i_preprocessed;
    ansi_c_scanner_init();
    result=ansi_c_parser.parse();
  }

  // save result
  parse_tree.swap(ansi_c_parser.parse_tree);

  // save some memory
  ansi_c_parser.clear();

  return result;
}

/*******************************************************************\

Function: ansi_c_languaget::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ansi_c_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module)
{
  symbol_tablet new_symbol_table;

  if(ansi_c_typecheck(
    parse_tree,
    new_symbol_table,
    module,
    get_message_handler()))
  {
    return true;
  }

  remove_internal_symbols(new_symbol_table);

  if(linking(symbol_table, new_symbol_table, get_message_handler()))
    return true;

  return false;
}

/*******************************************************************\

Function: ansi_c_languaget::final

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ansi_c_languaget::final(
  symbol_tablet &symbol_table,
  bool generate_start_function)
{
  if(generate_start_function)
  {
    if(ansi_c_entry_point(symbol_table, "main", get_message_handler()))
      return true;
  }

  return false;
}

/*******************************************************************\

Function: ansi_c_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_languaget::show_parse(std::ostream &out)
{
  parse_tree.output(out);
}

/*******************************************************************\

Function: new_ansi_c_language

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

languaget *new_ansi_c_language()
{
  return new ansi_c_languaget;
}

/*******************************************************************\

Function: ansi_c_languaget::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ansi_c_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr2c(expr, ns);
  return false;
}

/*******************************************************************\

Function: ansi_c_languaget::from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ansi_c_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type2c(type, ns);
  return false;
}

/*******************************************************************\

Function: ansi_c_languaget::get_pretty_printer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::unique_ptr<pretty_printert>
ansi_c_languaget::get_pretty_printer(const namespacet &ns)
{
  return std::unique_ptr<pretty_printert>(new expr2ct(ns));
}

/*******************************************************************\

Function: ansi_c_languaget::type_to_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ansi_c_languaget::type_to_name(
  const typet &type,
  std::string &name,
  const namespacet &ns)
{
  name=type2name(type, ns);
  return false;
}

/*******************************************************************\

Function: ansi_c_languaget::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ansi_c_languaget::to_expr(
  const std::string &code,
  const std::string &module,
  exprt &expr,
  const namespacet &ns)
{
  expr.make_nil();

  // no preprocessing yet...

  std::istringstream i_preprocessed(
    "void __my_expression = (void) (\n"+code+"\n);");

  // parsing

  ansi_c_parser.clear();
  ansi_c_parser.set_file(irep_idt());
  ansi_c_parser.in=&i_preprocessed;
  ansi_c_parser.set_message_handler(get_message_handler());
  ansi_c_parser.mode=config.ansi_c.mode;
  ansi_c_scanner_init();

  bool result=ansi_c_parser.parse();

  if(ansi_c_parser.parse_tree.items.empty())
    result=true;
  else
  {
    expr=ansi_c_parser.parse_tree.items.front().declarator().value();

    // typecheck it
    result=ansi_c_typecheck(expr, get_message_handler(), ns);
  }

  // save some memory
  ansi_c_parser.clear();

  // now remove that (void) cast
  if(expr.id()==ID_typecast &&
     expr.type().id()==ID_empty &&
     expr.operands().size()==1)
    expr=expr.op0();

  return result;
}

/*******************************************************************\

Function: ansi_c_languaget::~ansi_c_languaget

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ansi_c_languaget::~ansi_c_languaget()
{
}
