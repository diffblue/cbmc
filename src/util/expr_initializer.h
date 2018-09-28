/*******************************************************************\

Module: Expression Initialization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Expression Initialization

#ifndef CPROVER_UTIL_EXPR_INITIALIZER_H
#define CPROVER_UTIL_EXPR_INITIALIZER_H

#include "expr.h"
#include "optional.h"

class message_handlert;
class namespacet;
class source_locationt;

optionalt<exprt>
zero_initializer(const typet &, const source_locationt &, const namespacet &);

optionalt<exprt> nondet_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns);

#endif // CPROVER_UTIL_EXPR_INITIALIZER_H
