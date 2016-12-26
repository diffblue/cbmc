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
  exprt operator()(const exprt &);

protected:
  // to produce a fresh ID for each new let
  std::size_t let_id_count = 0;

  struct let_count_idt
  {
    let_count_idt(std::size_t _count, const symbol_exprt &_let_symbol)
      : count(_count), let_symbol(_let_symbol)
    {
    }

    std::size_t count;
    symbol_exprt let_symbol;
  };

#if HASH_CODE
  using seen_expressionst = std::unordered_map<exprt, let_count_idt, irep_hash>;
#else
  using seen_expressionst = irep_hash_mapt<exprt, let_count_idt>;
#endif

  void collect_bindings(
    const exprt &expr,
    seen_expressionst &map,
    std::vector<exprt> &let_order);

  static exprt letify(
    const exprt &expr,
    const std::vector<exprt> &let_order,
    const seen_expressionst &map);

  static exprt substitute_let(const exprt &expr, const seen_expressionst &map);
};

#endif // CPROVER_SOLVERS_SMT2_LETIFY_H
