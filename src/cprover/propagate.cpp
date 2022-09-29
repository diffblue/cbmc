/*******************************************************************\

Module: Propagate

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Propagate

#include "propagate.h"

#include <util/format_expr.h>
#include <util/simplify_expr.h>

#include "simplify_state_expr.h"
#include "state.h"

#include <iostream>

void propagate(
  const std::vector<framet> &frames,
  const workt &work,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  bool verbose,
  const namespacet &ns,
  const std::function<void(const symbol_exprt &, exprt, const workt::patht &)>
    &propagator)
{
  if(verbose)
  {
    std::cout << "PROP";
    for(const auto &p : work.path)
      std::cout << ' ' << p.index;
    std::cout << ": " << format(work.invariant) << '\n';
  }

  auto &f = frames[work.frame.index];

  for(const auto &implication : f.implications)
  {
    auto &next_state = implication.rhs.arguments().front();
    auto lambda_expr = lambda_exprt({state_expr()}, work.invariant);
    auto instance = lambda_expr.instantiate({next_state});
    auto simplified1 = simplify_state_expr(instance, address_taken, ns);
    auto simplified1a = simplify_state_expr(simplified1, address_taken, ns);
    if(simplified1 != simplified1a)
    {
      std::cout << "SIMP0: " << format(instance) << "\n";
      std::cout << "SIMP1: " << format(simplified1) << "\n";
      std::cout << "SIMPa: " << format(simplified1a) << "\n";
      abort();
    }
    auto simplified2 = simplify_expr(simplified1, ns);

    if(implication.lhs.id() == ID_function_application)
    {
      // Sxx(ς) ⇒ Syy(ς[update])
      auto &state = to_symbol_expr(
        to_function_application_expr(implication.lhs).function());
      propagator(state, simplified2, work.path);
    }
    else if(
      implication.lhs.id() == ID_and &&
      to_and_expr(implication.lhs).op0().id() == ID_function_application)
    {
      // Sxx(ς) ∧ ς(COND) ⇒ Syy(ς)
      auto &function_application =
        to_function_application_expr(to_and_expr(implication.lhs).op0());
      auto &state = to_symbol_expr(function_application.function());
      auto cond = to_and_expr(implication.lhs).op1();
      propagator(state, implies_exprt(cond, simplified2), work.path);
    }
  }
}
