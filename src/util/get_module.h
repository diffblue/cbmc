/*******************************************************************\

Module: Find module symbol using name

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Find module symbol using name

#ifndef CPROVER_UTIL_GET_MODULE_H
#define CPROVER_UTIL_GET_MODULE_H

#include <string>

class symbol_tablet;
class message_handlert;
class symbolt;

const symbolt &get_module(
  const symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler);

#endif // CPROVER_UTIL_GET_MODULE_H
