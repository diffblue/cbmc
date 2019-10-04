/// Author: Diffblue Ltd.

#include "symbol_table.h"

#include <algorithm>
#include <util/invariant.h>
#include <util/validate.h>

#include <set>

/// Move or copy a new symbol to the symbol table.
/// \remarks This is a nicer interface than move and achieves the same
///   result as both move and add.
/// \param symbol: The symbol to be added to the symbol table - can be
///   moved or copied in.
/// \return Returns a reference to the newly inserted symbol or to the
///   existing symbol if a symbol with the same name already exists in the
///   symbol table, along with a bool that is true if a new symbol was inserted.
std::pair<symbolt &, bool> symbol_tablet::insert(symbolt symbol)
{
  // Add the symbol to the table or retrieve existing symbol with the same name
  std::pair<symbolst::iterator, bool> result=
    internal_symbols.emplace(symbol.name, std::move(symbol));
  symbolt &new_symbol=result.first->second;
  if(result.second)
  {
    try
    {
      internal_symbol_base_map.emplace(new_symbol.base_name, new_symbol.name);
    }
    catch(...)
    {
      internal_symbols.erase(result.first);
      throw;
    }
  }
  return std::make_pair(std::ref(new_symbol), result.second);
}

/// Move a symbol into the symbol table. If there is already a symbol with the
/// same name then symbol is unchanged, new_symbol points to the symbol with the
/// same name and true is returned. Otherwise, the symbol is moved into the
/// symbol table, symbol is destroyed, new_symbol points to its new
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
  symbolt temp_symbol;
  // This is not copying the symbol, this is passing the three required
  // parameters to insert (just in the symbol)
  temp_symbol.name=symbol.name;
  temp_symbol.base_name=symbol.base_name;
  temp_symbol.module=symbol.module;
  std::pair<symbolt &, bool> result=insert(std::move(temp_symbol));
  if(result.second)
  {
    // Move the provided symbol into the symbol table, this can't be done
    // earlier
    result.first.swap(symbol);
  }
  // Return the address of the symbol in the table
  new_symbol=&result.first;
  return !result.second;
}

/// Remove a symbol from the symbol table.
/// \param entry: an iterator pointing at the symbol to remove
void symbol_tablet::erase(const symbolst::const_iterator &entry)
{
  const symbolt &symbol=entry->second;

  symbol_base_mapt::const_iterator
    base_it=symbol_base_map.lower_bound(entry->second.base_name);
  symbol_base_mapt::const_iterator
    base_it_end=symbol_base_map.upper_bound(entry->second.base_name);
  while(base_it!=base_it_end && base_it->second!=symbol.name)
    ++base_it;
  INVARIANT(
    base_it!=base_it_end,
    "symbolt::base_name should not be changed "
    "after it is added to the symbol_table "
    "(name: "+id2string(symbol.name)+", "
    "current base_name: "+id2string(symbol.base_name)+")");
  internal_symbol_base_map.erase(base_it);

  internal_symbols.erase(entry);
}

/// Check whether the symbol table is in a valid state
/// \param vm: Determine whether to throw exceptions or trigger INVARIANT
///   when validation fails.
void symbol_tablet::validate(const validation_modet vm) const
{
  // Check that identifiers are mapped to the correct symbol
  for(const auto &elem : symbols)
  {
    const auto symbol_key = elem.first;
    const auto &symbol = elem.second;

    // First of all, ensure symbol well-formedness
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm, symbol.is_well_formed(), "Symbol is malformed: ", symbol_key);

    // Check that symbols[id].name == id
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      symbol.name == symbol_key,
      "Symbol table entry must map to a symbol with the correct identifier",
      "Symbol table key '",
      symbol_key,
      "' maps to symbol '",
      symbol.name,
      "'");

    // Check that the symbol basename is mapped to its full name
    if(!symbol.base_name.empty())
    {
      const auto base_map_search =
        symbol_base_map.equal_range(symbol.base_name);
      const bool base_map_matches_symbol =
        std::find_if(
          base_map_search.first,
          base_map_search.second,
          [&symbol_key](const symbol_base_mapt::value_type &match) {
            return match.second == symbol_key;
          }) != symbol_base_map.end();

      DATA_CHECK_WITH_DIAGNOSTICS(
        vm,
        base_map_matches_symbol,
        "The base_name of a symbol should map to itself",
        "Symbol table key '",
        symbol_key,
        "' has a base_name '",
        symbol.base_name,
        "' which does not map to itself");
    }
  }

  // Check that all base name map entries point to a symbol entry
  for(auto base_map_entry : symbol_base_map)
  {
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      has_symbol(base_map_entry.second),
      "Symbol table base_name map entries must map to a symbol name",
      "base_name map entry '",
      base_map_entry.first,
      "' maps to non-existant symbol name '",
      base_map_entry.second,
      "'");
  }
}

bool symbol_tablet::operator==(const symbol_tablet &other) const
{
  // we cannot use == for comparing the multimaps as it compares the items
  // sequentially, but the order of items with equal keys depends on the
  // insertion order

  {
    std::vector<std::pair<irep_idt, irep_idt>> v1(
      internal_symbol_base_map.begin(), internal_symbol_base_map.end());

    std::vector<std::pair<irep_idt, irep_idt>> v2(
      other.internal_symbol_base_map.begin(),
      other.internal_symbol_base_map.end());

    std::sort(v1.begin(), v1.end());
    std::sort(v2.begin(), v2.end());

    if(v1 != v2)
      return false;
  }

  return internal_symbols == other.internal_symbols;
}
