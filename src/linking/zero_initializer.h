/*******************************************************************\

Module: Linking: Zero Initialization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LINKING_ZERO_INITIALIZER_H
#define CPROVER_LINKING_ZERO_INITIALIZER_H

#include <util/expr.h>
#include <util/namespace.h>
#include <util/message.h>

exprt zero_initializer(
  const typet &,
  const source_locationt &,
  const namespacet &,
  message_handlert &);

#endif // CPROVER_LINKING_ZERO_INITIALIZER_H
