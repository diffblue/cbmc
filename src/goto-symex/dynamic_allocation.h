/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DYNAMIC_ALLOCATION_H
#define CPROVER_DYNAMIC_ALLOCATION_H

#include <util/expr.h>
#include <util/namespace.h>

void replace_dynamic_allocation(
  const namespacet &ns,
  exprt &expr);

#endif
