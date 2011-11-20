/*******************************************************************\

Module: Find module symbol using name

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <string>

class contextt;
class message_handlert;
class symbolt;

const symbolt &get_module(
  const contextt &context,
  const std::string &module,
  message_handlert &message_handler);
