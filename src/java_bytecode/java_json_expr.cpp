/*******************************************************************\

Module: Expressions in JSON for Java

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Expressions in JSON for Java

#include "java_json_expr.h"

#include <util/std_expr.h>

#include <langapi/language.h>

/// Output a Java source location in json.
/// \param location: a source location
/// \return a json object
json_objectt java_json_exprt::operator()(const source_locationt &location)
{
  json_objectt result = json_exprt()(location);

  if(!location.get_java_bytecode_index().empty())
    result["bytecodeIndex"] =
      json_stringt(id2string(location.get_java_bytecode_index()));

  return result;
}

/// Output a Java constant expression as a string.
/// \param ns: a namespace
/// \param expr: a constant expression
/// \return a string
std::string
java_json_exprt::from_constant(const namespacet &ns, const constant_exprt &expr)
{
  std::string result;
  language->from_expr(expr, result, ns);
  return result;
}

/// Output a Java type as a string.
/// \param ns: a namespace
/// \param type: an type
/// \return a string
std::string java_json_exprt::from_type(const namespacet &ns, const typet &type)
{
  std::string result;
  language->from_type(type, result, ns);
  return result;
}
