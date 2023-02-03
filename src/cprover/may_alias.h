/*******************************************************************\

Module: Solver

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// May Alias

#ifndef CPROVER_CPROVER_MAY_ALIAS_H
#define CPROVER_CPROVER_MAY_ALIAS_H

#include <util/std_expr.h> // IWYU pragma: keep

#include <unordered_set>

class namespacet;

bool is_object_field_element(const exprt &);

// check whether the given two addresses may be aliases
optionalt<exprt> may_alias(
  const exprt &,
  const exprt &,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &);

bool stack_and_not_dirty(
  const exprt &,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &);

#endif // CPROVER_CPROVER_MAY_ALIAS_H
