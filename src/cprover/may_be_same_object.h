/*******************************************************************\

Module: May Be Same Object

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// May Be Same Object

#ifndef CPROVER_CPROVER_MAY_BE_SAME_OBJECT_H
#define CPROVER_CPROVER_MAY_BE_SAME_OBJECT_H

#include <util/std_expr.h>

#include <unordered_set>

class namespacet;

// check whether the given two addresses may point to same object
exprt may_be_same_object(
  const exprt &,
  const exprt &,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &);

#endif // CPROVER_CPROVER_MAY_BE_SAME_OBJECT_H
