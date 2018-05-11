/*******************************************************************\

Module: Zero Initialization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Zero Initialization

#ifndef CPROVER_UTIL_ZERO_INITIALIZER_H
#define CPROVER_UTIL_ZERO_INITIALIZER_H

#include "expr.h"

class message_handlert;
class namespacet;
class source_locationt;

exprt zero_initializer(
  const typet &,
  const source_locationt &,
  const namespacet &,
  message_handlert &);

// throws a char* in case of failure
exprt zero_initializer(
  const typet &,
  const source_locationt &,
  const namespacet &);

#endif // CPROVER_UTIL_ZERO_INITIALIZER_H
