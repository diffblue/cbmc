/*******************************************************************\

Module: Fresh auxiliary symbol creation

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_FRESH_SYMBOL_H
#define CPROVER_UTIL_FRESH_SYMBOL_H

#include <string>

#include <util/irep.h>
#include <util/source_location.h>
#include <util/symbol_table.h>
#include <util/type.h>

symbolt &get_fresh_aux_symbol(
  const typet &type,
  const std::string &name_prefix,
  const std::string &basename_prefix,
  const source_locationt &source_location,
  const irep_idt &symbol_mode,
  symbol_tablet &symbol_table);

#endif // CPROVER_UTIL_FRESH_SYMBOL_H
