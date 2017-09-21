/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "symbol_table.h"

#include <ostream>

/// Add a new symbol to the symbol table
/// \param symbol: The symbol to be added to the symbol table
/// \return Returns true if the process failed, which should only happen if
///   there is a symbol with the same name already in the symbol table.
bool symbol_tablet::add(const symbolt &symbol)
{
  std::pair<symbolst::iterator, bool> result=
    symbols.emplace(symbol.name, symbol);
  if(!result.second)
    return true;
  add_base_and_module(result.first);
  return false;
}

/// Move a new symbol to the symbol table
/// \remark: This is a nicer interface than move but achieves the same result
/// \param symbol: The symbol to be added to the symbol table
/// \return Returns an optional reference to the newly inserted symbol, without
///   a value if a symbol with the same name already exists in the symbol table
optionalt<std::reference_wrapper<symbolt>> symbol_tablet::insert(
  symbolt &&symbol)
{
  // Add the symbol to the table or retrieve existing symbol with the same name
  std::pair<symbolst::iterator, bool> result=
    symbols.emplace(symbol.name, std::move(symbol));
  if(!result.second)
    return optionalt<std::reference_wrapper<symbolt>>();
  add_base_and_module(result.first);
  return std::ref(result.first->second);
}

/// Move a symbol into the symbol table. If there is already a symbol with the
/// same name then symbol is unchanged, new_symbol points to the symbol with the
/// same name and true is returned. Otherwise, the symbol is moved into the
/// symbol table, symbol is set to be empty, new_symbol points to its new
/// location in the symbol table and false is returned
/// \param symbol: The symbol to be added to the symbol table
/// \param new_symbol: Pointer which the function will set to either point to
///   the symbol in the symbol table with the same name or to the symbol that
///   has been successfully moved into the symbol table
/// \return Returns a boolean indicating whether the process failed, which
///   should only happen if there is a symbol with the same name already in the
///   symbol table. If the process failed then symbol is unchanged and
///   new_symbol points to the symbol with the same name. If the process
///   succeeded symbol is set to be empty and new_symbol points to its new
///   location in the symbol table
bool symbol_tablet::move(symbolt &symbol, symbolt *&new_symbol)
{
  // Add an empty symbol to the table or retrieve existing symbol with same name
  std::pair<symbolst::iterator, bool> result=
    symbols.emplace(symbol.name, symbolt());

  if(!result.second)
  {
    // Return the address of the symbol that already existed in the table
    new_symbol=&result.first->second;
    return true;
  }

  // Move the provided symbol into the symbol table
  result.first->second.swap(symbol);

  add_base_and_module(result.first);

  // Return the address of the new symbol in the table
  new_symbol=&result.first->second;

  return false;
}

void symbol_tablet::add_base_and_module(symbolst::iterator added_symbol)
{
  symbolt &symbol=added_symbol->second;
  try
  {
    symbol_base_mapt::iterator base_result=
      symbol_base_map.emplace(symbol.base_name, symbol.name);
    try
    {
      symbol_module_map.emplace(symbol.module, symbol.name);
    }
    catch(...)
    {
      symbol_base_map.erase(base_result);
      throw;
    }
  }
  catch(...)
  {
    symbols.erase(added_symbol);
    throw;
  }
}

/// Remove a symbol from the symbol table
/// \param name: The name of the symbol to remove
/// \return Returns a boolean indicating whether the process failed
bool symbol_tablet::remove(const irep_idt &name)
{
  symbolst::iterator entry=symbols.find(name);

  if(entry==symbols.end())
    return true;

  for(symbol_base_mapt::iterator
      it=symbol_base_map.lower_bound(entry->second.base_name),
      it_end=symbol_base_map.upper_bound(entry->second.base_name);
      it!=it_end;
      ++it)
    if(it->second==name)
    {
      symbol_base_map.erase(it);
      break;
    }

  for(symbol_module_mapt::iterator
      it=symbol_module_map.lower_bound(entry->second.module),
      it_end=symbol_module_map.upper_bound(entry->second.module);
      it!=it_end;
      ++it)
    if(it->second==name)
    {
      symbol_module_map.erase(it);
      break;
    }

  symbols.erase(entry);

  return false;
}

/// Print the contents of the symbol table
/// \param out: The ostream to direct output to
void symbol_tablet::show(std::ostream &out) const
{
  out << "\n" << "Symbols:" << "\n";

  forall_symbols(it, symbols)
    out << it->second;
}

/// Find a symbol in the symbol table. Throws a string if no such symbol is
/// found.
/// \param identifier: The name of the symbol to look for
/// \return The symbol in the symbol table with the correct name
const symbolt &symbol_tablet::lookup(const irep_idt &identifier) const
{
  symbolst::const_iterator it=symbols.find(identifier);

  if(it==symbols.end())
    throw "symbol "+id2string(identifier)+" not found";

  return it->second;
}

/// Find a symbol in the symbol table. Throws a string if no such symbol is
/// found.
/// \param identifier: The name of the symbol to look for
/// \return The symbol in the symbol table with the correct name
symbolt &symbol_tablet::lookup(const irep_idt &identifier)
{
  symbolst::iterator it=symbols.find(identifier);

  if(it==symbols.end())
    throw "symbol "+id2string(identifier)+" not found";

  return it->second;
}

/// Print the contents of the symbol table
/// \param out: The ostream to direct output to
/// \param symbol_table: The symbol table to print out
std::ostream &operator << (std::ostream &out, const symbol_tablet &symbol_table)
{
  symbol_table.show(out);
  return out;
}
