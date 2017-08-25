/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/


#ifndef CPROVER_LANGAPI_LANGUAGE_UTIL_H
#define CPROVER_LANGAPI_LANGUAGE_UTIL_H

#include <memory>
#include <functional>

#include <util/irep.h>
#include <langapi/pretty_printer.h>

class exprt;
class namespacet;
class typet;

std::string from_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const exprt &expr);

std::string from_expr(const exprt &expr);

std::string from_type(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type);

std::string from_type(const typet &type);

typedef std::function<std::unique_ptr<pretty_printert>(const namespacet &)>
  pretty_printer_factoryt;

void register_global_pretty_printer(pretty_printer_factoryt);

exprt to_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const std::string &src);

std::string type_to_name(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type);

std::string type_to_name(const typet &type);

#endif // CPROVER_LANGAPI_LANGUAGE_UTIL_H
