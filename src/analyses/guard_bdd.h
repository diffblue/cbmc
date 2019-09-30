/*******************************************************************\

Module: Guard Data Structure

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Guard Data Structure
/// Implementation using BDDs

#ifndef CPROVER_ANALYSES_GUARD_BDD_H
#define CPROVER_ANALYSES_GUARD_BDD_H

#include <iosfwd>
#include <memory>

#include <solvers/bdd/bdd.h>
#include <solvers/prop/bdd_expr.h>
#include <util/make_unique.h>
#include <util/std_expr.h>

class guard_bddt
{
public:
  guard_bddt(const exprt &e, bdd_exprt &manager);
  guard_bddt(const guard_bddt &other) : manager(other.manager), bdd(other.bdd)
  {
  }

  guard_bddt &operator=(const guard_bddt &other);
  guard_bddt &operator=(guard_bddt &&other);
  guard_bddt &add(const exprt &expr);
  guard_bddt &append(const guard_bddt &guard);
  exprt as_expr() const;

  /// BDDs are always in a simplified form and thus no further simplification
  /// is required after calls to \ref as_expr().
  /// This can vary according to the guard implementation.
  static constexpr bool is_always_simplified = true;

  /// Return `guard => dest` or a simplified variant thereof if either guard or
  /// dest are trivial.
  exprt guard_expr(exprt expr) const;

  bool is_true() const
  {
    return bdd.is_true();
  }

  bool is_false() const
  {
    return bdd.is_false();
  }

  /// Transforms \p g1 into \c g1' such that `g1' & g2 => g1 => g1'`
  /// and returns a reference to g1.
  friend guard_bddt &operator-=(guard_bddt &g1, const guard_bddt &g2);

  friend guard_bddt &operator|=(guard_bddt &g1, const guard_bddt &g2);

  guard_bddt operator!() const
  {
    return guard_bddt(manager, bdd.bdd_not());
  }

  /// Returns true if `operator|=` with \p other_guard may result in a simpler
  /// expression. For `bdd_exprt` we always simplify maximally.
  bool disjunction_may_simplify(const guard_bddt &other_guard)
  {
    return true;
  }

private:
  bdd_exprt &manager;
  bddt bdd;

  guard_bddt(bdd_exprt &manager, bddt bdd)
    : manager(manager), bdd(std::move(bdd))
  {
  }
};

#endif // CPROVER_ANALYSES_GUARD_BDD_H
