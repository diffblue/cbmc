/*******************************************************************\

Module: Find module symbol using name

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <context.h>
#include <message.h>

const symbolt &get_module(
  const contextt &context,
  const std::string &module,
  message_handlert &message_handler);
