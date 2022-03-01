/*******************************************************************\

Module: Variable Encoding

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Variable Encoding

#include "variable_encoding.h"

#include <util/exception_utils.h>
#include <util/format_expr.h>
#include <util/mathematical_expr.h>
#include <util/pointer_expr.h>

#include "find_variables.h"
#include "state.h"

#include <algorithm>

exprt variable_encoding(exprt src, const binding_exprt::variablest &variables)
{
  // operands first
  for(auto &op : src.operands())
    op = variable_encoding(op, variables);

  if(src.id() == ID_forall)
  {
    auto &forall_expr = to_forall_expr(src);
    if(
      forall_expr.variables().size() == 1 &&
      forall_expr.symbol().type().id() == ID_state)
    {
      forall_expr
        .variables() = variables;
      return std::move(forall_expr);
    }
  }
  else if(src.id() == ID_function_application)
  {
    auto &function_application = to_function_application_expr(src);
    if(
      function_application.arguments().size() == 1 &&
      function_application.arguments().front().type().id() == ID_state)
    {
      if(function_application.arguments().front().id() == ID_symbol)
      {
        exprt::operandst new_arguments;
        for(auto &v : variables)
          new_arguments.push_back(v);
        function_application.arguments() = new_arguments;
      }
      else if(function_application.arguments().front().id() == ID_tuple)
      {
        DATA_INVARIANT(
          function_application.arguments().front().operands().size() ==
            variables.size(),
          "tuple size must match");
        auto operands = function_application.arguments().front().operands();
        function_application.arguments() = operands;
      }
      else
        throw analysis_exceptiont("can't convert " + format_to_string(src));
    }
    else
      throw analysis_exceptiont("can't convert " + format_to_string(src));
  }
  else if(src.id() == ID_evaluate)
  {
    auto &evaluate_expr = to_evaluate_expr(src);
    if(evaluate_expr.address().id() == ID_object_address)
      return symbol_exprt(
        to_object_address_expr(evaluate_expr.address()).object_expr());
    else
      throw analysis_exceptiont("can't convert " + format_to_string(src));
  }
  else if(src.id() == ID_update_state)
  {
    auto &update_state_expr = to_update_state_expr(src);
    if(update_state_expr.address().id() == ID_object_address)
    {
      auto lhs_symbol =
        to_object_address_expr(update_state_expr.address()).object_expr();
      exprt::operandst operands;
      for(auto &v : variables)
      {
        if(v == lhs_symbol)
          operands.push_back(update_state_expr.new_value());
        else
          operands.push_back(v);
      }
      return tuple_exprt(operands, typet(ID_state));
    }
    else
      throw analysis_exceptiont("can't convert " + format_to_string(src));
  }

  return src;
}

void variable_encoding(std::vector<exprt> &constraints)
{
  binding_exprt::variablest variables;

  for(auto &v : find_variables(constraints))
    variables.push_back(v);

  if(variables.empty())
    throw analysis_exceptiont("no variables found");

  // sort alphabetically
  std::sort(
    variables.begin(),
    variables.end(),
    [](const symbol_exprt &a, const symbol_exprt &b) {
      return id2string(a.get_identifier()) < id2string(b.get_identifier());
    });

  for(auto &c : constraints)
    c = variable_encoding(c, variables);
}
