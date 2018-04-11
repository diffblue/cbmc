/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include "language_util.h"

#include <memory>

#include <util/symbol_table.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include "language.h"
#include "mode.h"

std::string from_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const exprt &expr)
{
  std::unique_ptr<languaget> p(
    get_language_from_identifier(ns, identifier));

  std::string result;
  p->from_expr(expr, result, ns);

  return result;
}

std::string from_type(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type)
{
  std::unique_ptr<languaget> p(
    get_language_from_identifier(ns, identifier));

  std::string result;
  p->from_type(type, result, ns);

  return result;
}

json_objectt json(
  const namespacet &ns,
  const irep_idt &identifier,
  const exprt &expr)
{
  std::unique_ptr<languaget> p(
    get_language_from_identifier(ns, identifier));

  std::string result;
  return p->json(expr, ns);
}

json_objectt json(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type)
{
  std::unique_ptr<languaget> p(
    get_language_from_identifier(ns, identifier));

  return p->json(type, ns);
}

std::string type_to_name(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type)
{
  std::unique_ptr<languaget> p(
    get_language_from_identifier(ns, identifier));

  std::string result;
  p->type_to_name(type, result, ns);

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
  std::unique_ptr<languaget> p(
    get_language_from_identifier(ns, identifier));

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
  return type_to_name(namespacet(symbol_table), "", type);
}

json_objectt json(
  const namespacet &ns,
  const irep_idt &identifier,
  const source_locationt &source_location)
{
  std::unique_ptr<languaget> p(
    get_language_from_identifier(ns, identifier));

  return p->json(source_location);
}
