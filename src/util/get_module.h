/*******************************************************************\

Module: Find module symbol using name

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <string>

class symbol_tablet;
class message_handlert;
class symbolt;

const symbolt &get_module(
  const symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler);
