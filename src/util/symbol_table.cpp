/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "symbol_table.h"

/*******************************************************************\

Function: symbol_tablet::add

 Inputs:
  symbol - The symbol to be added to the symbol table

 Outputs: Returns a boolean indicating whether the process failed,
          which should only happen if there is a symbol with the same
          name already in the symbol table

 Purpose: Add a new symbol to the symbol table

\*******************************************************************/

bool symbol_tablet::add(const symbolt &symbol)
{
  if(!symbols.insert(std::pair<irep_idt, symbolt>(symbol.name, symbol)).second)
    return true;

  symbol_base_map.insert(
    std::pair<irep_idt, irep_idt>(symbol.base_name, symbol.name));
  symbol_module_map.insert(
    std::pair<irep_idt, irep_idt>(symbol.module, symbol.name));

  return false;
}

/*******************************************************************\

Function: symbol_tablet::move

 Inputs:
  symbol - The symbol to be added to the symbol table
  new_symbol - Pointer which the function will set to either point
               to the symbol in the symbol table with the same name
               or to the symbol that has been successfully moved
               into the symbol table

 Outputs: Returns a boolean indicating whether the process failed,
          which should only happen if there is a symbol with the
          same name already in the symbol table. If the process
          failed then symbol is unchanged and new_symbol points to
          the symbol with the same name. If the process succeeded
          symbol is set to be empty and new_symbol points to its new
          location in the symbol table

 Purpose: Move a symbol into the symbol table. If there is already
          a symbol with the same name then symbol is unchanged,
          new_symbol points to the symbol with the same name and
          true is returned. Otherwise, the symbol is moved into the
          symbol table, symbol is set to be empty, new_symbol points
          to its new location in the symbol table and false is
          returned

\*******************************************************************/

bool symbol_tablet::move(symbolt &symbol, symbolt *&new_symbol)
{
  symbolt tmp;

  std::pair<symbolst::iterator, bool> result=
    symbols.insert(std::pair<irep_idt, symbolt>(symbol.name, tmp));

  if(!result.second)
  {
    new_symbol=&result.first->second;
    return true;
  }

  symbol_base_map.insert(
    std::pair<irep_idt, irep_idt>(symbol.base_name, symbol.name));
  symbol_module_map.insert(
    std::pair<irep_idt, irep_idt>(symbol.module, symbol.name));

  result.first->second.swap(symbol);
  new_symbol=&result.first->second;

  return false;
}

/*******************************************************************\

Function: symbol_tablet::remove

 Inputs:
  name - The name of the symbol to remove

 Outputs: Returns a boolean indicating whether the process failed

 Purpose: Remove a symbol from the symbol table

\*******************************************************************/

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

/*******************************************************************\

Function: symbol_tablet::show

 Inputs:
  out - The ostream to direct output to

 Outputs:

 Purpose: Print the contents of the symbol table

\*******************************************************************/

void symbol_tablet::show(std::ostream &out) const
{
  out << "\n" << "Symbols:" << "\n";

  forall_symbols(it, symbols)
    out << it->second;
}

/*******************************************************************\

Function: symbol_tablet::lookup

 Inputs:
  identifier - The name of the symbol to look for

 Outputs: The symbol in the symbol table with the correct name

 Purpose: Find a symbol in the symbol table. Throws a string if no
          such symbol is found.

\*******************************************************************/

const symbolt &symbol_tablet::lookup(const irep_idt &identifier) const
{
  return lookup(*this, identifier);
}

/*******************************************************************\

Function: symbol_tablet::lookup

 Inputs:
  identifier - The name of the symbol to look for

 Outputs: The symbol in the symbol table with the correct name

 Purpose: Find a symbol in the symbol table. Throws a string if no
          such symbol is found.

\*******************************************************************/

symbolt &symbol_tablet::lookup(const irep_idt &identifier)
{
  return lookup(*this, identifier);
}

/*******************************************************************\

Function: operator <<

 Inputs:
  out - The ostream to direct output to
  symbol_table - The symbol table to print out

 Outputs:

 Purpose: Print the contents of the symbol table

\*******************************************************************/

std::ostream &operator << (std::ostream &out, const symbol_tablet &symbol_table)
{
  symbol_table.show(out);
  return out;
}
