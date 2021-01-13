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

static optionalt<exprt> substitute_symbols_rec(
  const std::map<irep_idt, exprt> &substitutions,
  exprt src)
{
  if(src.id() == ID_symbol)
  {
    auto s_it = substitutions.find(to_symbol_expr(src).get_identifier());
    if(s_it == substitutions.end())
      return {};
    else
      return s_it->second;
  }

  if(!src.has_operands())
    return {};

  bool op_changed = false;

  for(auto &op : src.operands())
  {
    auto op_result = substitute_symbols_rec(substitutions, op);

    if(op_result.has_value())
    {
      op = op_result.value();
      op_changed = true;
    }
  }

  if(op_changed)
    return src;
  else
    return {};
}

exprt lambda_exprt::application(const operandst &arguments) const
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

  // build a subsitution map
  std::map<irep_idt, exprt> substitutions;

  for(std::size_t i = 0; i < variables.size(); i++)
    substitutions[variables[i].get_identifier()] = arguments[i];

  // now recurse downwards and substitute in 'where'
  auto substitute_result = substitute_symbols_rec(substitutions, where());

  if(substitute_result.has_value())
    return substitute_result.value();
  else
    return where(); // trivial case, variables not used
}
