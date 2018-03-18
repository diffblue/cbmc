/*******************************************************************\

Module: Expressions in JSON for Java

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Expressions in JSON for Java

#ifndef CPROVER_JAVA_BYTECODE_JAVA_JSON_EXPR_H
#define CPROVER_JAVA_BYTECODE_JAVA_JSON_EXPR_H

#include <util/json_expr.h>

#include <langapi/mode.h>

class java_json_exprt : public json_exprt
{
public:
  json_objectt operator()(
    const exprt &expr,
    const namespacet &ns) override
  {
    return json_exprt::operator()(expr, ns);
  }

  json_objectt operator()(
    const typet &type,
    const namespacet &ns) override
  {
    return json_exprt::operator()(type, ns);
  }

  json_objectt operator()(const source_locationt &) override;

protected:
  std::unique_ptr<languaget> language = get_language_from_mode(ID_java);
  std::string from_constant(const namespacet &ns, const constant_exprt &) override;
  std::string from_type(const namespacet &ns, const typet &) override;
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_JSON_EXPR_H
