/*******************************************************************\

Module: Fresh auxiliary symbol creation

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Fresh auxiliary symbol creation

#include "fresh_symbol.h"

#include "invariant.h"
#include "namespace.h"
#include "rename.h"
#include "symbol.h"
#include "symbol_table_base.h"

/// Installs a fresh-named symbol with respect to the given namespace `ns` with
/// the requested name pattern in the given symbol table
/// \param type: The type of the new symbol.
/// \param name_prefix: The new symbol will be named
///   `name_prefix::basename_prefix$num` unless name_prefix is empty, in which
///   case the :: prefix is omitted.
/// \param basename_prefix: See `name_prefix`.
/// \param source_location: The source location for the new symbol.
/// \param symbol_mode: The mode for the new symbol, e.g. ID_C, ID_java.
/// \param ns: the new symbol has a different name than any symbols in `ns`
/// \param symbol_table: The symbol table to add the new symbol to.
/// \return The new symbol.
symbolt &get_fresh_aux_symbol(
  const typet &type,
  const std::string &name_prefix,
  const std::string &basename_prefix,
  const source_locationt &source_location,
  const irep_idt &symbol_mode,
  const namespacet &ns,
  symbol_table_baset &symbol_table)
{
  irep_idt identifier = basename_prefix;
  std::size_t prefix_size = 0;
  if(!name_prefix.empty())
  {
    identifier = name_prefix + "::" + basename_prefix;
    prefix_size = name_prefix.size() + 2;
  }
  identifier = get_new_name(identifier, ns, '$');
  std::string basename = id2string(identifier).substr(prefix_size);

  auxiliary_symbolt new_symbol(identifier, type, symbol_mode);
  new_symbol.base_name = basename;
  new_symbol.location = source_location;
  std::pair<symbolt &, bool> res = symbol_table.insert(std::move(new_symbol));
  CHECK_RETURN(res.second);

  return res.first;
}

/// Installs a fresh-named symbol with the requested name pattern in the given
/// symbol table
/// \param type: The type of the new symbol.
/// \param name_prefix: The new symbol will be named
///   `name_prefix::basename_prefix$num` unless name_prefix is empty, in which
///   case the :: prefix is omitted.
/// \param basename_prefix: See `name_prefix`.
/// \param source_location: The source location for the new symbol.
/// \param symbol_mode: The mode for the new symbol, e.g. ID_C, ID_java.
/// \param symbol_table: The symbol table to add the new symbol to.
/// \return The new symbol.
symbolt &get_fresh_aux_symbol(
  const typet &type,
  const std::string &name_prefix,
  const std::string &basename_prefix,
  const source_locationt &source_location,
  const irep_idt &symbol_mode,
  symbol_table_baset &symbol_table)
{
  return get_fresh_aux_symbol(
    type,
    name_prefix,
    basename_prefix,
    source_location,
    symbol_mode,
    namespacet(symbol_table),
    symbol_table);
}
