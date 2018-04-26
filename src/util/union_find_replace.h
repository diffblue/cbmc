/*******************************************************************\

Module: util

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_UNION_FIND_REPLACE_H
#define CPROVER_UTIL_UNION_FIND_REPLACE_H

#include "replace_expr.h"

/// Similar interface to union-find for expressions, with a function for
/// replacing sub-expressions by their result for find.
class union_find_replacet
{
public:
  bool replace_expr(exprt &expr) const;

  exprt find(exprt expr) const;

  exprt make_union(const exprt &a, const exprt &b);

  std::vector<std::pair<exprt, exprt>> to_vector() const;

private:
  replace_mapt map;
};

#endif // CPROVER_UTIL_UNION_FIND_REPLACE_H
