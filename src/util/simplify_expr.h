/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_SIMPLIFY_EXPR_H
#define CPROVER_UTIL_SIMPLIFY_EXPR_H

class exprt;
class namespacet;

//
// simplify an expression
//
// true: did nothing
// false: simplified something
//

bool simplify(
  exprt &expr,
  const namespacet &ns);

// this is the preferred interface
exprt simplify_expr(exprt src, const namespacet &ns);

#endif // CPROVER_UTIL_SIMPLIFY_EXPR_H
