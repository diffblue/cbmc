/*******************************************************************\

Module: Fresh auxiliary symbol creation

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Fresh auxiliary symbol creation

#ifndef CPROVER_UTIL_FRESH_SYMBOL_H
#define CPROVER_UTIL_FRESH_SYMBOL_H

#include <string>

#include "irep.h"

class namespacet;
class source_locationt;
class symbolt;
class symbol_table_baset;
class typet;

symbolt &get_fresh_aux_symbol(
  const typet &type,
  const std::string &name_prefix,
  const std::string &basename_prefix,
  const source_locationt &source_location,
  const irep_idt &symbol_mode,
  symbol_table_baset &symbol_table);

symbolt &get_fresh_aux_symbol(
  const typet &type,
  const std::string &name_prefix,
  const std::string &basename_prefix,
  const source_locationt &source_location,
  const irep_idt &symbol_mode,
  const namespacet &ns,
  symbol_table_baset &symbol_table);

#endif // CPROVER_UTIL_FRESH_SYMBOL_H
