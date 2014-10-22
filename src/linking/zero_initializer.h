/*******************************************************************\

Module: Linking: Zero Initialization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/expr.h>
#include <util/namespace.h>
#include <util/message.h>

exprt zero_initializer(
  const typet &,
  const source_locationt &,
  const namespacet &,
  message_handlert &);
