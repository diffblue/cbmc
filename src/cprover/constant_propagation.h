/*******************************************************************\

Module: Constant Propagation

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Constant Propagation

#ifndef CPROVER_CPROVER_CONSTANT_PROPAGATION_H
#define CPROVER_CPROVER_CONSTANT_PROPAGATION_H

#include <util/expr.h>

/// Propagates the values of constant program variables in a CHC system
void constant_propagation(std::vector<exprt> &);

#endif // CPROVER_CPROVER_CONSTANT_PROPAGATION_H
