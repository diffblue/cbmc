/*******************************************************************\

Module: API to expression classes for 'mathematical' expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "mathematical_expr.h"
#include "mathematical_types.h"

#include <map>

function_application_exprt::function_application_exprt(
  const exprt &_function,
  argumentst _arguments)
  : binary_exprt(
      _function,
      ID_function_application,
      tuple_exprt(std::move(_arguments)),
      to_mathematical_function_type(_function.type()).codomain())
{
  const auto &domain = function_type().domain();
  PRECONDITION(domain.size() == arguments().size());
}

const mathematical_function_typet &
function_application_exprt::function_type() const
{
  return to_mathematical_function_type(function().type());
}

static mathematical_function_typet
lambda_type(const lambda_exprt::variablest &variables, const exprt &where)
{
  mathematical_function_typet::domaint domain;

  domain.reserve(variables.size());

  for(const auto &v : variables)
    domain.push_back(v.type());

  return mathematical_function_typet(std::move(domain), where.type());
}

lambda_exprt::lambda_exprt(const variablest &_variables, const exprt &_where)
  : binding_exprt(
      ID_lambda,
      _variables,
      _where,
      lambda_type(_variables, _where))
{
}
