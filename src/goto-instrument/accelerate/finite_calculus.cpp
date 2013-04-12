/*
 * Routines for doing finite calculus.
 */

#include "finite_calculus.h"

#include <replace_expr.h>

#include <assert.h>

exprt indefinite_sum(const exprt &e, const exprt &x) {
  assert(!"indefinite_sum() not implemented");
}

exprt definite_sum(const exprt &e, const exprt &x, const exprt &lower,
                   const exprt &upper) {
  // If the indefinite sum is solved by S:
  //
  //  S = \sum e \delta x
  //
  // then the definite sum is defined as:
  //
  //  \sum_{lower}^{upper} e \delta x = S[upper/x] - S[lower/x]

  exprt S = indefinite_sum(e, x);
  exprt v1 = S;
  exprt v2 = S;

  replace_expr(x, upper, v1);
  replace_expr(x, lower, v2);

  return minus_exprt(v1, v2);
}

exprt difference(exprt &e, exprt &x) {
  assert(!"difference() not implemented");
}
