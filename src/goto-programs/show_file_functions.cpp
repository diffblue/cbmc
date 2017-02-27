/*******************************************************************\

Module: Show the functions present in the file

Author: Fotis Koutoulakis

\*******************************************************************/

#include <iostream>
#include <memory>
#include <string>
#include <set>

#include <util/namespace.h>
#include <util/language.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#include "show_file_functions.h"

/*******************************************************************\

Function: show_file_functions

  Inputs:

 Outputs:

 Purpose: Filter symbol table information so that only symbols that 
          correspond to functions are output.

\*******************************************************************/

void show_file_functions(std::ostream &out, const symbol_tablet &symbol_table)
{
  // in order to sort the symbols alphabetically
  std::set<std::string> symbols;

  for(const auto &symbol_entry : symbol_table.symbols)
    symbols.insert(id2string(symbol_entry.first));
  
  const namespacet ns(symbol_table);

  for(const std::string &id : symbols)
  {    
    const symbolt &symbol=ns.lookup(id);

    if (!(symbol.type.id() == ID_code))
      continue;

    if (!(symbol.is_file_local))
      continue;

    out << "Function: " << symbol.name << '\n';
    out << '\n' << std::flush;
  }
}

  
