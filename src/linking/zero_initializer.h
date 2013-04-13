/*******************************************************************\

Module: Linking: Zero Initialization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/expr.h>
#include <util/namespace.h>
#include <util/message.h>

exprt zero_initializer(
  const typet &type,
  const locationt &location,
  const namespacet &ns,
  message_handlert &message_handler);
