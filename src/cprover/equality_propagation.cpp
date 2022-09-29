/*******************************************************************\

Module: Equality Propagation

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Equality Propagation

#include "equality_propagation.h"

#include <util/std_expr.h>
#include <util/substitute_symbols.h>

void equality_propagation(std::vector<exprt> &constraints)
{
  using valuest = std::map<irep_idt, exprt>;
  valuest values;

  std::vector<exprt> new_constraints;
  new_constraints.reserve(constraints.size());

  // forward-propagation of equalities
  for(auto &expr : constraints)
  {
    bool retain_constraint = true;

    // apply the map
    auto substitution_result = substitute_symbols(values, expr);
    if(substitution_result.has_value())
      expr = std::move(substitution_result.value());

    if(expr.id() == ID_equal)
    {
      const auto &equal_expr = to_equal_expr(expr);
      if(equal_expr.lhs().id() == ID_symbol)
      {
        const auto &symbol_expr = to_symbol_expr(equal_expr.lhs());
        // this is a (deliberate) no-op when the symbol is already in the map
        auto insert_result =
          values.insert({symbol_expr.get_identifier(), equal_expr.rhs()});
        if(insert_result.second)
        {
          // insertion has happened
          retain_constraint = false;
        }
      }
    }

    if(retain_constraint)
      new_constraints.push_back(std::move(expr));
  }

  constraints = std::move(new_constraints);

  // apply the map again, to catch any backwards definitions
  for(auto &expr : constraints)
  {
    if(expr.id() == ID_equal && to_equal_expr(expr).lhs().id() == ID_symbol)
    {
      // it's a definition
    }
    else
    {
      // apply the map
      auto substitution_result = substitute_symbols(values, expr);
      if(substitution_result.has_value())
        expr = std::move(substitution_result.value());
    }
  }
}
