/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include "language_util.h"

#include <util/invariant.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include "language.h"
#include "mode.h"

#include <memory>

std::string from_expr_using_mode(
  const namespacet &ns,
  const irep_idt &mode,
  const exprt &expr)
{
  std::unique_ptr<languaget> language = (mode == ID_unknown)
                                          ? get_default_language()
                                          : get_language_from_mode(mode);
  INVARIANT(
    language, "could not retrieve language for mode '" + id2string(mode) + "'");

  std::string result;
  language->from_expr(expr, result, ns);

  return result;
}

std::string from_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const exprt &expr)
{
  std::unique_ptr<languaget> p(get_language_from_identifier(ns, identifier));

  std::string result;
  p->from_expr(expr, result, ns);

  return result;
}

std::string from_type(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type)
{
  std::unique_ptr<languaget> p(get_language_from_identifier(ns, identifier));

  std::string result;
  p->from_type(type, result, ns);

  return result;
}

std::string type_to_name(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type)
{
  std::unique_ptr<languaget> p(get_language_from_identifier(ns, identifier));

  std::string result;
  p->type_to_name(type, result, ns);

  return result;
}

std::string from_expr(const exprt &expr)
{
  symbol_tablet symbol_table;
  return from_expr(namespacet(symbol_table), irep_idt(), expr);
}

std::string from_type(const typet &type)
{
  symbol_tablet symbol_table;
  return from_type(namespacet(symbol_table), irep_idt(), type);
}

exprt to_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const std::string &src)
{
  std::unique_ptr<languaget> p(get_language_from_identifier(ns, identifier));

  null_message_handlert null_message_handler;
  p->set_message_handler(null_message_handler);

  const symbolt &symbol=ns.lookup(identifier);

  exprt expr;

  if(p->to_expr(src, id2string(symbol.module), expr, ns))
    return nil_exprt();

  return expr;
}

std::string type_to_name(const typet &type)
{
  symbol_tablet symbol_table;
  return type_to_name(namespacet(symbol_table), irep_idt(), type);
}
