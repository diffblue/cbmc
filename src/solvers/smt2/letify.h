/*******************************************************************\

Module: Introduce LET for common subexpressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SMT2_LETIFY_H
#define CPROVER_SOLVERS_SMT2_LETIFY_H

#include <util/irep_hash_container.h>
#include <util/std_expr.h>

/// Introduce LET for common subexpressions
class letifyt
{
public:
  exprt operator()(exprt &expr);

protected:
  // to produce a fresh ID for each new let
  std::size_t let_id_count = 0;

  static const std::size_t LET_COUNT = 2;

  struct let_count_idt
  {
    let_count_idt(std::size_t _count, const symbol_exprt &_let_symbol)
      : count(_count), let_symbol(_let_symbol)
    {
    }

    std::size_t count;
    symbol_exprt let_symbol;
  };

#ifdef HASH_CODE
  using seen_expressionst = std::unordered_map<exprt, let_count_idt, irep_hash>;
#else
  using seen_expressionst = irep_hash_mapt<exprt, let_count_idt>;
#endif

  class let_visitort : public expr_visitort
  {
    const seen_expressionst &let_map;

  public:
    explicit let_visitort(const seen_expressionst &map) : let_map(map)
    {
    }

    void operator()(exprt &expr)
    {
      seen_expressionst::const_iterator it = let_map.find(expr);
      if(it != let_map.end() && it->second.count >= letifyt::LET_COUNT)
      {
        const symbol_exprt &symb = it->second.let_symbol;
        expr = symb;
      }
    }
  };

  void collect_bindings(
    exprt &expr,
    seen_expressionst &map,
    std::vector<exprt> &let_order);

  exprt letify_rec(
    exprt &expr,
    std::vector<exprt> &let_order,
    const seen_expressionst &map,
    std::size_t i);

  exprt substitute_let(exprt &expr, const seen_expressionst &map);
};

#endif // CPROVER_SOLVERS_SMT2_LETIFY_H
