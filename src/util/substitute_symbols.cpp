/*******************************************************************\

Module: Symbol Substitution

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file util/substitute_symbols.cpp
/// Symbol Substitution

#include "substitute_symbols.h"

#include "std_expr.h"

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
  else if(
    src.id() == ID_forall || src.id() == ID_exists || src.id() == ID_lambda)
  {
    const auto &binding_expr = to_binding_expr(src);

    // bindings may be nested,
    // which may hide some of our substitutions
    auto new_substitutions = substitutions;
    for(const auto &variable : binding_expr.variables())
      new_substitutions.erase(variable.get_identifier());

    auto op_result =
      substitute_symbols_rec(new_substitutions, binding_expr.where());
    if(op_result.has_value())
    {
      auto new_binding_expr = binding_expr; // copy
      new_binding_expr.where() = std::move(op_result.value());
      return std::move(new_binding_expr);
    }
    else
      return {};
  }
  else if(src.id() == ID_let)
  {
    auto new_let_expr = to_let_expr(src); // copy
    const auto &binding_expr = to_let_expr(src).binding();

    // bindings may be nested,
    // which may hide some of our substitutions
    auto new_substitutions = substitutions;
    for(const auto &variable : binding_expr.variables())
      new_substitutions.erase(variable.get_identifier());

    bool op_changed = false;

    for(auto &op : new_let_expr.values())
    {
      auto op_result = substitute_symbols_rec(new_substitutions, op);

      if(op_result.has_value())
      {
        op = op_result.value();
        op_changed = true;
      }
    }

    auto op_result =
      substitute_symbols_rec(new_substitutions, binding_expr.where());
    if(op_result.has_value())
    {
      new_let_expr.where() = op_result.value();
      op_changed = true;
    }

    if(op_changed)
      return std::move(new_let_expr);
    else
      return {};
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

optionalt<exprt>
substitute_symbols(const std::map<irep_idt, exprt> &substitutions, exprt src)
{
  return substitute_symbols_rec(substitutions, src);
}
