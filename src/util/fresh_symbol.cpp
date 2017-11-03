/*******************************************************************\

Module: Fresh auxiliary symbol creation

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Fresh auxiliary symbol creation

#include "fresh_symbol.h"

// This needs to be outside get_fresh_aux_symbol
// to make it available for both reset_temporary_counter
// and get_fresh_aux_symbol
static size_t temporary_counter=0;

// This is useful with loading multiple GOTO models
void reset_temporary_counter()
{
  temporary_counter=0;
}

/// Installs a fresh-named symbol with the requested name pattern
/// \par parameters: `type`: type of new symbol
/// `name_prefix`, `basename_prefix`: new symbol will be named
///   name_prefix::basename_prefix$num unless name_prefix is empty, in which
///   case the :: prefix is omitted.
/// `source_location`: new symbol source loc
/// `symbol_mode`: new symbol mode
/// `symbol_table`: table to add the new symbol to
symbolt &get_fresh_aux_symbol(
  const typet &type,
  const std::string &name_prefix,
  const std::string &basename_prefix,
  const source_locationt &source_location,
  const irep_idt &symbol_mode,
  symbol_table_baset &symbol_table)
{
  // Loop until find a name that doesn't clash with a non-auxilliary symbol
  while(true)
  {
    auxiliary_symbolt new_symbol(
      // Distinguish local variables with the same name
      basename_prefix + "$" + std::to_string(++temporary_counter),
      type);
    if(!name_prefix.empty())
      new_symbol.name=name_prefix+"::"+id2string(new_symbol.base_name);
    new_symbol.location=source_location;
    new_symbol.mode=symbol_mode;
    std::pair<symbolt &, bool> res=symbol_table.insert(std::move(new_symbol));
    if(res.second)
      return res.first;
  }
}
