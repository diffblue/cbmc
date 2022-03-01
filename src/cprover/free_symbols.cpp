/*******************************************************************\

Module: Free Symbols

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file util/substitute_symbols.cpp
/// Free Symbols

#include "free_symbols.h"

#include <unordered_set>

static void free_symbols_rec(
  const std::unordered_set<symbol_exprt, irep_hash> &bound_symbols,
  const exprt &src,
  const std::function<void(const symbol_exprt &)> &f)
{
  if(src.id() == ID_symbol)
  {
    const auto &symbol_expr = to_symbol_expr(src);
    auto b_it = bound_symbols.find(symbol_expr);
    if(b_it == bound_symbols.end())
      f(symbol_expr);
  }
  else if(
    src.id() == ID_forall || src.id() == ID_exists || src.id() == ID_lambda)
  {
    // bindings may hide symbols
    const auto &binding_expr = to_binding_expr(src);

    auto new_bound_symbols = bound_symbols; // copy

    for(const auto &s : binding_expr.variables())
      new_bound_symbols.insert(s);

    free_symbols_rec(new_bound_symbols, binding_expr.where(), f);
  }
  else if(src.id() == ID_let)
  {
    // bindings may hide symbols
    const auto &let_expr = to_let_expr(src);

    for(const auto &v : let_expr.values())
      free_symbols_rec(bound_symbols, v, f);

    auto new_bound_symbols = bound_symbols; // copy

    for(const auto &s : let_expr.variables())
      new_bound_symbols.insert(s);

    free_symbols_rec(new_bound_symbols, let_expr.where(), f);
  }
  else
  {
    for(const auto &op : src.operands())
      free_symbols_rec(bound_symbols, op, f);
  }
}

void free_symbols(
  const exprt &expr,
  const std::function<void(const symbol_exprt &)> &f)
{
  std::unordered_set<symbol_exprt, irep_hash> free_symbols, bound_symbols;
  free_symbols_rec(bound_symbols, expr, f);
}
