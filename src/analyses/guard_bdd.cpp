/*******************************************************************\

Module: Guard Data Structure

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Implementation of guards using BDDs

#include "guard_bdd.h"

#include <algorithm>
#include <ostream>
#include <set>

#include <solvers/bdd/bdd.h>
#include <solvers/prop/bdd_expr.h>
#include <util/expr_util.h>
#include <util/invariant.h>
#include <util/make_unique.h>
#include <util/namespace.h>
#include <util/simplify_utils.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

guard_bddt::guard_bddt(const exprt &e, bdd_exprt &manager)
  : manager(manager), bdd(manager.from_expr(e))
{
}

guard_bddt &guard_bddt::operator=(const guard_bddt &other)
{
  PRECONDITION(&manager == &other.manager);
  bdd = other.bdd;
  return *this;
}

guard_bddt &guard_bddt::operator=(guard_bddt &&other)
{
  PRECONDITION(&manager == &other.manager);
  std::swap(bdd, other.bdd);
  return *this;
}

exprt guard_bddt::guard_expr(exprt expr) const
{
  if(is_true())
  {
    // do nothing
    return expr;
  }
  else
  {
    if(expr.is_false())
    {
      return boolean_negate(as_expr());
    }
    else
    {
      return implies_exprt{as_expr(), expr};
    }
  }
}

guard_bddt &guard_bddt::append(const guard_bddt &guard)
{
  bdd = bdd.bdd_and(guard.bdd);
  return *this;
}

guard_bddt &guard_bddt::add(const exprt &expr)
{
  bdd = bdd.bdd_and(manager.from_expr(expr));
  return *this;
}

guard_bddt &operator-=(guard_bddt &g1, const guard_bddt &g2)
{
  g1.bdd = g1.bdd.constrain(g2.bdd.bdd_or(g1.bdd));
  return g1;
}

guard_bddt &operator|=(guard_bddt &g1, const guard_bddt &g2)
{
  g1.bdd = g1.bdd.bdd_or(g2.bdd);
  return g1;
}

exprt guard_bddt::as_expr() const
{
  return manager.as_expr(bdd);
}
