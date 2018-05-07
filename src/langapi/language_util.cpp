/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include "language_util.h"

#include <memory>

#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include "language.h"
#include "language_info.h"
#include "mode.h"

std::string from_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const exprt &expr)
{
  const auto &language_info = get_language_info_from_identifier(ns, identifier);

  std::string result;
  language_info.from_expr(expr, result, ns);

  return result;
}

std::string from_type(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type)
{
  const auto &language_info = get_language_info_from_identifier(ns, identifier);

  std::string result;
  language_info.from_type(type, result, ns);

  return result;
}

std::string type_to_name(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type)
{
  const auto &language_info = get_language_info_from_identifier(ns, identifier);

  std::string result;
  language_info.type_to_name(type, result, ns);

  return result;
}

std::string from_expr(const exprt &expr)
{
  symbol_tablet symbol_table;
  return from_expr(namespacet(symbol_table), "", expr);
}

std::string from_type(const typet &type)
{
  symbol_tablet symbol_table;
  return from_type(namespacet(symbol_table), "", type);
}

exprt to_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const std::string &src)
{
  std::unique_ptr<languaget> language =
    get_language_from_identifier(ns, identifier);

  const symbolt &symbol=ns.lookup(identifier);

  exprt expr;

  if(language->to_expr(src, id2string(symbol.module), expr, ns))
    return nil_exprt();

  return expr;
}

std::string type_to_name(const typet &type)
{
  symbol_tablet symbol_table;
  return type_to_name(namespacet(symbol_table), "", type);
}
