/*******************************************************************\

Module: Linking: Zero Initialization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <expr.h>
#include <namespace.h>
#include <message.h>

exprt zero_initializer(
  const typet &type,
  const locationt &location,
  const namespacet &ns,
  message_handlert &message_handler);
