/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ansi_c_language.h"

#include <util/config.h>
#include <util/get_base_name.h>
#include <util/symbol_table.h>

#include <linking/linking.h>
#include <linking/remove_internal_symbols.h>

#include "ansi_c_entry_point.h"
#include "ansi_c_internal_additions.h"
#include "ansi_c_parser.h"
#include "ansi_c_typecheck.h"
#include "c_preprocess.h"
#include "expr2c.h"
#include "type2name.h"

#include <fstream>

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
  std::ostream &outstream,
  message_handlert &message_handler)
{
  // stdin?
  if(path.empty())
    return c_preprocess(instream, outstream, message_handler);

  return c_preprocess(path, outstream, message_handler);
}

bool ansi_c_languaget::parse(
  std::istream &instream,
  const std::string &path,
  message_handlert &message_handler)
{
  // store the path
  parse_path=path;

  // preprocessing
  std::ostringstream o_preprocessed;

  if(preprocess(instream, path, o_preprocessed, message_handler))
    return true;

  std::istringstream i_preprocessed(o_preprocessed.str());

  // parsing

  std::string code;
  ansi_c_internal_additions(code, config.ansi_c.float16_type);
  std::istringstream codestr(code);

  ansi_c_parsert ansi_c_parser{message_handler};
  ansi_c_parser.set_file(ID_built_in);
  ansi_c_parser.in=&codestr;
  ansi_c_parser.for_has_scope=config.ansi_c.for_has_scope;
  ansi_c_parser.ts_18661_3_Floatn_types=config.ansi_c.ts_18661_3_Floatn_types;
  ansi_c_parser.__float128_is_keyword = config.ansi_c.__float128_is_keyword;
  ansi_c_parser.float16_type = config.ansi_c.float16_type;
  ansi_c_parser.bf16_type = config.ansi_c.bf16_type;
  ansi_c_parser.fp16_type = config.ansi_c.fp16_type;
  ansi_c_parser.cpp98=false; // it's not C++
  ansi_c_parser.cpp11=false; // it's not C++
  ansi_c_parser.mode=config.ansi_c.mode;

  ansi_c_scanner_init(ansi_c_parser);

  bool result=ansi_c_parser.parse();

  if(!result)
  {
    ansi_c_parser.set_line_no(0);
    ansi_c_parser.set_file(path);
    ansi_c_parser.in=&i_preprocessed;
    ansi_c_scanner_init(ansi_c_parser);
    result=ansi_c_parser.parse();
  }

  // save result
  parse_tree.swap(ansi_c_parser.parse_tree);

  return result;
}

bool ansi_c_languaget::typecheck(
  symbol_table_baset &symbol_table,
  const std::string &module,
  message_handlert &message_handler,
  const bool keep_file_local)
{
  return typecheck(symbol_table, module, message_handler, keep_file_local, {});
}

bool ansi_c_languaget::typecheck(
  symbol_table_baset &symbol_table,
  const std::string &module,
  message_handlert &message_handler,
  const bool keep_file_local,
  const std::set<irep_idt> &keep)
{
  symbol_tablet new_symbol_table;

  if(ansi_c_typecheck(parse_tree, new_symbol_table, module, message_handler))
  {
    return true;
  }

  remove_internal_symbols(
    new_symbol_table, message_handler, keep_file_local, keep);

  if(linking(symbol_table, new_symbol_table, message_handler))
    return true;

  return false;
}

bool ansi_c_languaget::generate_support_functions(
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  // This creates __CPROVER_start and __CPROVER_initialize:
  return ansi_c_entry_point(
    symbol_table, message_handler, object_factory_params);
}

void ansi_c_languaget::show_parse(std::ostream &out, message_handlert &)
{
  parse_tree.output(out);
}

std::unique_ptr<languaget> new_ansi_c_language()
{
  return std::make_unique<ansi_c_languaget>();
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
  const namespacet &ns,
  message_handlert &message_handler)
{
  expr.make_nil();

  // no preprocessing yet...

  std::istringstream i_preprocessed(
    "void __my_expression = (void) (\n"+code+"\n);");

  // parsing

  ansi_c_parsert ansi_c_parser{message_handler};
  ansi_c_parser.set_file(irep_idt());
  ansi_c_parser.in=&i_preprocessed;
  ansi_c_parser.for_has_scope = config.ansi_c.for_has_scope;
  ansi_c_parser.ts_18661_3_Floatn_types=config.ansi_c.ts_18661_3_Floatn_types;
  ansi_c_parser.__float128_is_keyword = config.ansi_c.__float128_is_keyword;
  ansi_c_parser.float16_type = config.ansi_c.float16_type;
  ansi_c_parser.bf16_type = config.ansi_c.bf16_type;
  ansi_c_parser.fp16_type = config.ansi_c.fp16_type;
  ansi_c_parser.cpp98 = false; // it's not C++
  ansi_c_parser.cpp11 = false; // it's not C++
  ansi_c_parser.mode = config.ansi_c.mode;
  ansi_c_scanner_init(ansi_c_parser);

  bool result=ansi_c_parser.parse();

  if(ansi_c_parser.parse_tree.items.empty())
    result=true;
  else
  {
    expr=ansi_c_parser.parse_tree.items.front().declarator().value();

    // typecheck it
    result = ansi_c_typecheck(expr, message_handler, ns);
  }

  // now remove that (void) cast
  if(expr.id()==ID_typecast &&
     expr.type().id()==ID_empty &&
     expr.operands().size()==1)
  {
    expr = to_typecast_expr(expr).op();
  }

  return result;
}

ansi_c_languaget::~ansi_c_languaget()
{
}
