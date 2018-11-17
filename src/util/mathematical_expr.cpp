/*******************************************************************\

Module: API to expression classes for 'mathematical' expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "mathematical_expr.h"
#include "mathematical_types.h"

function_application_exprt::function_application_exprt(
  const exprt &_function,
  argumentst _arguments)
  : binary_exprt(
      _function,
      ID_function_application,
      tuple_exprt(std::move(_arguments)),
      to_mathematical_function_type(_function.type()).codomain())
{
  const auto &domain = to_mathematical_function_type(_function.type()).domain();
  PRECONDITION(domain.size() == arguments().size());
}

static mathematical_function_typet
lambda_type(const lambda_exprt::variablest &variables, exprt where)
{
  mathematical_function_typet::domaint domain;

  domain.reserve(variables.size());

  for(const auto &v : variables)
    domain.push_back(v.type());

  return mathematical_function_typet(std::move(domain), where.type());
}

lambda_exprt::lambda_exprt(const variablest &_variables, exprt _where)
  : binary_exprt(
      tuple_exprt((const operandst &)_variables),
      ID_lambda,
      _where,
      lambda_type(_variables, _where))
{
}
