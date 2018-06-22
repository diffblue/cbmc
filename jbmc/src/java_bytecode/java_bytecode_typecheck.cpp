/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Conversion / Type Checking

#include "java_bytecode_typecheck.h"

#include <util/std_types.h>
#include <util/prefix.h>
#include <util/config.h>

#include "expr2java.h"

std::string java_bytecode_typecheckt::to_string(const exprt &expr)
{
  return expr2java(expr, ns);
}

std::string java_bytecode_typecheckt::to_string(const typet &type)
{
  return type2java(type, ns);
}

void java_bytecode_typecheckt::typecheck_non_type_symbol(symbolt &symbol)
{
  assert(!symbol.is_type);
  typecheck_type(symbol.type);
  typecheck_expr(symbol.value);
}

void java_bytecode_typecheckt::typecheck()
{
  // The hash table iterators are not stable,
  // and we might add new symbols.
  journalling_symbol_tablet::changesett identifiers;
  identifiers.reserve(symbol_table.symbols.size());
  for(const auto &symbol_pair : symbol_table.symbols)
    identifiers.insert(symbol_pair.first);
  typecheck(identifiers);
}

void java_bytecode_typecheckt::typecheck(
  const journalling_symbol_tablet::changesett &identifiers)
{
  // We first check all type symbols,
  // recursively doing base classes first.
  for(const irep_idt &id : identifiers)
  {
    symbolt &symbol=*symbol_table.get_writeable(id);
    if(symbol.is_type)
      typecheck_type_symbol(symbol);
  }
  // We now check all non-type symbols
  for(const irep_idt &id : identifiers)
  {
    symbolt &symbol=*symbol_table.get_writeable(id);
    if(!symbol.is_type)
      typecheck_non_type_symbol(symbol);
  }
}

bool java_bytecode_typecheck(
  symbol_table_baset &symbol_table,
  message_handlert &message_handler,
  bool string_refinement_enabled)
{
  java_bytecode_typecheckt java_bytecode_typecheck(
    symbol_table, message_handler, string_refinement_enabled);
  return java_bytecode_typecheck.typecheck_main();
}

void java_bytecode_typecheck_updated_symbols(
  journalling_symbol_tablet &symbol_table,
  message_handlert &message_handler,
  bool string_refinement_enabled)
{
  java_bytecode_typecheckt java_bytecode_typecheck(
    symbol_table, message_handler, string_refinement_enabled);
  return java_bytecode_typecheck.typecheck(symbol_table.get_updated());
}

bool java_bytecode_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns)
{
  #if 0
  symbol_tablet symbol_table;
  java_bytecode_parse_treet java_bytecode_parse_tree;

  java_bytecode_typecheckt java_bytecode_typecheck(
    java_bytecode_parse_tree, symbol_table,
    "", message_handler);

  try
  {
    java_bytecode_typecheck.typecheck_expr(expr);
  }

  catch(int e)
  {
    java_bytecode_typecheck.error();
  }

  catch(const char *e)
  {
    java_bytecode_typecheck.error(e);
  }

  catch(const std::string &e)
  {
    java_bytecode_typecheck.error(e);
  }

  return java_bytecode_typecheck.get_error_found();
  #else
  // unused parameters
  (void)expr;
  (void)message_handler;
  (void)ns;
  #endif

  // fail for now
  return true;
}
