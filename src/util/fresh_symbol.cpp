/*******************************************************************\

Module: Fresh auxiliary symbol creation

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Fresh auxiliary symbol creation

#include "fresh_symbol.h"

#include "namespace.h"
#include "rename.h"

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
  namespacet ns(symbol_table);
  irep_idt identifier = basename_prefix;
  std::size_t prefix_size = 0;
  if(!name_prefix.empty())
  {
    identifier = name_prefix + "::" + basename_prefix;
    prefix_size = name_prefix.size() + 2;
  }
  get_new_name(identifier, ns, '$');
  std::string basename = id2string(identifier).substr(prefix_size);

  auxiliary_symbolt new_symbol(basename, type);
  new_symbol.name = identifier;
  new_symbol.location = source_location;
  new_symbol.mode = symbol_mode;
  std::pair<symbolt &, bool> res = symbol_table.insert(std::move(new_symbol));
  CHECK_RETURN(res.second);

  return res.first;
}
