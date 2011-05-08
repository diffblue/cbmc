/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DYNAMIC_ALLOCATION_H
#define CPROVER_DYNAMIC_ALLOCATION_H

#include <expr.h>
#include <namespace.h>

void replace_dynamic_allocation(
  const namespacet &ns,
  exprt &expr);

#endif
