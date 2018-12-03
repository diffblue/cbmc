/*******************************************************************\

Module: Abstract interface to support a programming language

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract interface to support a programming language

#include "language.h"

#include <util/expr.h>
#include <util/symbol.h>
#include <util/symbol_table.h>
#include <util/prefix.h>
#include <util/cprover_prefix.h>
#include <util/std_types.h>

bool languaget::final(symbol_table_baset &)
{
  return false;
}

bool languaget::interfaces(symbol_tablet &)
{
  return false;
}

void languaget::dependencies(
  const std::string &,
  std::set<std::string> &)
{
}

bool languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &)
{
  code=expr.pretty();
  return false;
}

bool languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &)
{
  code=type.pretty();
  return false;
}

bool languaget::type_to_name(
  const typet &type,
  std::string &name,
  const namespacet &)
{
  // probably ansi-c/type2name could be used as better fallback if moved to
  // util/
  name=type.pretty();
  return false;
}
