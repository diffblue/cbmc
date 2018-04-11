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
class json_objectt;
class source_locationt;

std::string from_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const exprt &expr);

std::string from_expr(const exprt &expr);

json_objectt json(
  const namespacet &ns,
  const irep_idt &identifier,
  const exprt &expr);

std::string from_type(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type);

std::string from_type(const typet &type);

json_objectt json(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type);

exprt to_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const std::string &src);

std::string type_to_name(
  const namespacet &ns,
  const irep_idt &identifier,  const typet &type);

std::string type_to_name(const typet &type);

json_objectt json(
  const namespacet &ns,
  const irep_idt &identifier,
  const source_locationt &source_location);

#endif // CPROVER_LANGAPI_LANGUAGE_UTIL_H
