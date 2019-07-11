/*******************************************************************\

Module: Rust Language

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/
// Adapted from the similarly named file in the jsil directory

/// \file
/// Rust Language

#include "rust_language.h"

#include <util/get_base_name.h>
#include <util/symbol_table.h>

#include "expr2rust.h"
#include "rust_convert.h"
#include "rust_entry_point.h"
#include "rust_internal_additions.h"
#include "rust_parser.h"
#include "rust_typecheck.h"

std::set<std::string> rust_languaget::extensions() const
{
  return {"rs"};
}

void rust_languaget::modules_provided(std::set<std::string> &modules)
{
  modules.insert(get_base_name(parse_path, true));
}

/// Adding symbols for all procedure declarations
bool rust_languaget::interfaces(symbol_tablet &symbol_table)
{
  if(rust_convert(parse_tree, symbol_table, get_message_handler()))
    return true;

  rust_internal_additions(symbol_table);

  return false;
}

bool rust_languaget::preprocess(
  std::istream &,
  const std::string &,
  std::ostream &)
{
  // there is no preprocessing!
  return true;
}

bool rust_languaget::parse(std::istream &instream, const std::string &path)
{
  // store the path
  parse_path = path;

  // parsing
  rust_parser.clear();
  rust_parser.set_file(path);
  rust_parser.in = &instream;
  rust_parser.set_message_handler(get_message_handler());

  rust_scanner_init();

  bool result = rust_parser.parse();

  // save result
  parse_tree.swap(rust_parser.parse_tree);

  // save some memory
  rust_parser.clear();

  return result;
}

/// Converting from parse tree and type checking.
bool rust_languaget::typecheck(symbol_tablet &symbol_table, const std::string &)
{
  if(rust_typecheck(symbol_table, get_message_handler()))
    return true;

  return false;
}

bool rust_languaget::generate_support_functions(symbol_tablet &symbol_table)
{
  return rust_entry_point(symbol_table, get_message_handler());
}

void rust_languaget::show_parse(std::ostream &out)
{
  parse_tree.output(out);
}

std::unique_ptr<languaget> new_rust_language()
{
  return util_make_unique<rust_languaget>();
}

bool rust_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code = expr2rust(expr, ns);
  return false;
}

bool rust_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code = type2rust(type, ns);
  return false;
}

bool rust_languaget::to_expr(
  const std::string &code,
  const std::string &,
  exprt &expr,
  const namespacet &ns)
{
  expr.make_nil();
  std::istringstream instream(code);

  // parsing

  rust_parser.clear();
  rust_parser.set_file(irep_idt());
  rust_parser.in = &instream;
  rust_parser.set_message_handler(get_message_handler());
  rust_scanner_init();

  bool result = rust_parser.parse();

  if(rust_parser.parse_tree.items.size() != 1)
    result = true;
  else
  {
    symbol_tablet symbol_table;
    result = rust_convert(parse_tree, symbol_table, get_message_handler());

    if(symbol_table.symbols.size() != 1)
      result = true;

    if(!result)
      expr = symbol_table.symbols.begin()->second.value;

    // typecheck it
    if(!result)
      result = rust_typecheck(expr, get_message_handler(), ns);
  }

  // save some memory
  rust_parser.clear();

  return result;
}

rust_languaget::~rust_languaget()
{
}
