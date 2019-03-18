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
  const exprt &expr,
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

exprt letifyt::letify(
  const exprt &expr,
  const std::vector<exprt> &let_order,
  const seen_expressionst &map)
{
  exprt result = substitute_let(expr, map);

  // go backwards in let order
  for(auto r_it = let_order.rbegin(); r_it != let_order.rend(); r_it++)
  {
    const exprt &current = *r_it;

    auto m_it = map.find(current);
    INVARIANT(m_it != map.end(), "expression should have been seen already");

    if(m_it->second.count >= LET_COUNT)
    {
      result = let_exprt(
        m_it->second.let_symbol, substitute_let(current, map), result);
    }
  }

  return result;
}

exprt letifyt::operator()(const exprt &expr)
{
  seen_expressionst map;
  std::vector<exprt> let_order;

  collect_bindings(expr, map, let_order);

  return letify(expr, let_order, map);
}

exprt letifyt::substitute_let(const exprt &expr, const seen_expressionst &map)
{
  if(expr.operands().empty())
    return expr;

  exprt tmp = expr;

  for(auto &op : tmp.operands())
  {
    op.visit([&map](exprt &expr) {
      seen_expressionst::const_iterator it = map.find(expr);
      if(it != map.end() && it->second.count >= letifyt::LET_COUNT)
        expr = it->second.let_symbol;
    });
  }

  return tmp;
}
