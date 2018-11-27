/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ansi_c_language.h"

#include <cstring>
#include <sstream>
#include <fstream>

#include <util/config.h>
#include <util/get_base_name.h>

#include <linking/linking.h>
#include <linking/remove_internal_symbols.h>

#include "ansi_c_entry_point.h"
#include "ansi_c_typecheck.h"
#include "ansi_c_parser.h"
#include "expr2c.h"
#include "c_preprocess.h"
#include "ansi_c_internal_additions.h"
#include "type2name.h"

std::set<std::string> ansi_c_languaget::extensions() const
{
  return { "c", "i" };
}

void ansi_c_languaget::modules_provided(std::set<std::string> &modules)
{
  modules.insert(get_base_name(parse_path, true));
}

/// ANSI-C preprocessing
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
  ansi_c_parser.ts_18661_3_Floatn_types=config.ansi_c.ts_18661_3_Floatn_types;
  ansi_c_parser.Float128_type = config.ansi_c.Float128_type;
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

bool ansi_c_languaget::generate_support_functions(
  symbol_tablet &symbol_table)
{
  // Note this can happen here because C doesn't currently
  // support lazy loading at the symbol-table level, and therefore
  // function bodies have already been populated and external stub
  // symbols created during the typecheck() phase. If it gains lazy
  // loading support then stubs will need to be created during
  // function body parsing, or else generate-stubs moved to the
  // final phase.
  generate_opaque_method_stubs(symbol_table);

  // This creates __CPROVER_start and __CPROVER_initialize:
  return ansi_c_entry_point(
    symbol_table, get_message_handler(), object_factory_params);
}

void ansi_c_languaget::show_parse(std::ostream &out)
{
  parse_tree.output(out);
}

std::unique_ptr<languaget> new_ansi_c_language()
{
  return util_make_unique<ansi_c_languaget>();
}

bool ansi_c_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr2c(expr, ns);
  return false;
}

bool ansi_c_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type2c(type, ns);
  return false;
}

bool ansi_c_languaget::type_to_name(
  const typet &type,
  std::string &name,
  const namespacet &ns)
{
  name=type2name(type, ns);
  return false;
}

bool ansi_c_languaget::to_expr(
  const std::string &code,
  const std::string &,
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
  ansi_c_parser.ts_18661_3_Floatn_types=config.ansi_c.ts_18661_3_Floatn_types;
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

ansi_c_languaget::~ansi_c_languaget()
{
}
