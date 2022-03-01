/*******************************************************************\

Module: Equality Propagation

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Equality Propagation

#ifndef CPROVER_CPROVER_EQUALITY_PROPAGATION_H
#define CPROVER_CPROVER_EQUALITY_PROPAGATION_H

#include <util/expr.h>

void equality_propagation(std::vector<exprt> &);

#endif // CPROVER_CPROVER_EQUALITY_PROPAGATION_H
