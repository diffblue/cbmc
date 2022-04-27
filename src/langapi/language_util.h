/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/


#ifndef CPROVER_LANGAPI_LANGUAGE_UTIL_H
#define CPROVER_LANGAPI_LANGUAGE_UTIL_H

#include <util/irep.h>

class exprt;
class namespacet;
class typet;

/// Formats an expression using the given namespace,
/// using the given mode to retrieve the language printer.
std::string from_expr_using_mode(
  const namespacet &ns,
  const irep_idt &mode,
  const exprt &expr);

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
