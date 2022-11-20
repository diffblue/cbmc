/*******************************************************************\

Module: Find Variables

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Find Variables

#ifndef CPROVER_CPROVER_FIND_VARIABLES_H
#define CPROVER_CPROVER_FIND_VARIABLES_H

#include <util/std_expr.h> // IWYU pragma: keep

#include <unordered_set>

/// Returns the set of program variables (as identified by object_address
/// expressions) in the given expression.
std::unordered_set<symbol_exprt, irep_hash>
find_variables(const std::vector<exprt> &);

#endif // CPROVER_CPROVER_FIND_VARIABLES_H
