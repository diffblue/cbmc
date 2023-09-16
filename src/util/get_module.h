/*******************************************************************\

Module: Find module symbol using name

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Find module symbol using name

#ifndef CPROVER_UTIL_GET_MODULE_H
#define CPROVER_UTIL_GET_MODULE_H

#include <string>

class symbol_table_baset;
class message_handlert;
class symbolt;

const symbolt &get_module(
  const symbol_table_baset &,
  const std::string &module,
  message_handlert &);

#endif // CPROVER_UTIL_GET_MODULE_H
