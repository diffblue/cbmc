/// Author: Diffblue Ltd.

#include "symbol_table_base.h"

#include <ostream>
#include <algorithm>

/// Destructor
symbol_table_baset::~symbol_table_baset()
{
}


/// Add a new symbol to the symbol table
/// \param symbol: The symbol to be added to the symbol table
/// \return Returns true if the process failed, which should only happen if
///   there is a symbol with the same name already in the symbol table.
bool symbol_table_baset::add(const symbolt &symbol)
{
  return !insert(symbol).second;
}

/// Remove a symbol from the symbol table
/// \param name: The name of the symbol to remove
/// \return Returns a boolean indicating whether the process failed
///   i.e. false if the symbol was removed, or true if it didn't exist.
bool symbol_table_baset::remove(const irep_idt &name)
{
  symbolst::const_iterator entry = symbols.find(name);
  if(entry == symbols.end())
    return true;
  erase(entry);
  return false;
}

/// Print the contents of the symbol table.
/// \param out: The ostream to direct output to.
void symbol_table_baset::show(std::ostream &out) const
{
  std::vector<irep_idt> sorted_names;
  sorted_names.reserve(symbols.size());
  for(const auto &elem : symbols)
    sorted_names.push_back(elem.first);
  std::sort(
    sorted_names.begin(),
    sorted_names.end(),
    [](const irep_idt &a, const irep_idt &b) { return a.compare(b); });
  out << "\n"
      << "Symbols:"
      << "\n";
  for(const auto &name : sorted_names)
    out << symbols.at(name);
}

/// Print the contents of the symbol table.
/// \param out: The ostream to direct output to
/// \param symbol_table: The symbol table to print out
std::ostream &
operator<<(std::ostream &out, const symbol_table_baset &symbol_table)
{
  symbol_table.show(out);
  return out;
}
