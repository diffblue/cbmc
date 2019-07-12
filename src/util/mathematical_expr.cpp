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

exprt lambda_exprt::application(const exprt::operandst &arguments) const
{
  // number of arguments must match function signature
  auto &variables = this->variables();
  PRECONDITION(variables.size() == arguments.size());

  std::map<symbol_exprt, exprt> value_map;

  for(std::size_t i = 0; i < variables.size(); i++)
  {
    // types must match
    PRECONDITION(variables[i].type() == arguments[i].type());
    value_map[variables[i]] = arguments[i];
  }

  // now recurse downwards and substitute in 'where'
  auto result =
    where().transform_pre([&value_map](exprt e) -> optionalt<exprt> {
      if(e.id() == ID_symbol)
      {
        const auto v_it = value_map.find(to_symbol_expr(e));
        if(v_it != value_map.end())
          return v_it->second;
        else
          return {};
      }
      else
        return {};
    });

  if(result.has_value())
    return std::move(result.value());
  else
    return where(); // trivial case, parameter is not used
}
