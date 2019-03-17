/*******************************************************************\

Module: Introduce LET for common subexpressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Introduce LET for common subexpressions

#include "letify.h"

#include <util/irep_hash_container.h>
#include <util/std_expr.h>

void letifyt::collect_bindings(
  exprt &expr,
  seen_expressionst &map,
  std::vector<exprt> &let_order)
{
  seen_expressionst::iterator entry = map.find(expr);

  if(entry != map.end())
  {
    let_count_idt &count_id = entry->second;
    ++(count_id.count);
    return;
  }

  // do not letify things with no children
  if(expr.operands().empty())
    return;

  for(auto &op : expr.operands())
    collect_bindings(op, map, let_order);

  INVARIANT(
    map.find(expr) == map.end(), "expression should not have been seen yet");

  symbol_exprt let =
    symbol_exprt("_let_" + std::to_string(++let_id_count), expr.type());

  map.insert(std::make_pair(expr, let_count_idt(1, let)));

  let_order.push_back(expr);
}

exprt letifyt::letify_rec(
  exprt &expr,
  std::vector<exprt> &let_order,
  const seen_expressionst &map,
  std::size_t i)
{
  if(i >= let_order.size())
    return substitute_let(expr, map);

  exprt current = let_order[i];
  INVARIANT(
    map.find(current) != map.end(), "expression should have been seen already");

  if(map.find(current)->second.count < LET_COUNT)
    return letify_rec(expr, let_order, map, i + 1);

  return let_exprt(
    map.find(current)->second.let_symbol,
    substitute_let(current, map),
    letify_rec(expr, let_order, map, i + 1));
}

exprt letifyt::operator()(exprt &expr)
{
  seen_expressionst map;
  std::vector<exprt> let_order;

  collect_bindings(expr, map, let_order);

  return letify_rec(expr, let_order, map, 0);
}

exprt letifyt::substitute_let(exprt &expr, const seen_expressionst &map)
{
  if(expr.operands().empty())
    return expr;

  let_visitort lv(map);

  for(auto &op : expr.operands())
    op.visit(lv);

  return expr;
}
