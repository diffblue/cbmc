/*******************************************************************\

Module: Fresh auxiliary symbol creation

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#include "fresh_symbol.h"

/*******************************************************************\

Function: get_fresh_aux_symbol

  Inputs: `type`: type of new symbol
          `name_prefix`, `basename_prefix`:
            new symbol will be named name_prefix::basename_prefix$num
            unless name_prefix is empty, in which case the :: prefix
            is omitted.
          `source_location`: new symbol source loc
          `symbol_mode`: new symbol mode
          `symbol_table`: table to add the new symbol to

 Outputs:

 Purpose: Installs a fresh-named symbol with the requested name pattern

\*******************************************************************/

symbolt &get_fresh_aux_symbol(
  const typet &type,
  const std::string &name_prefix,
  const std::string &basename_prefix,
  const source_locationt &source_location,
  const irep_idt &symbol_mode,
  symbol_tablet &symbol_table)
{
  static size_t temporary_counter=0;
  auxiliary_symbolt new_symbol;
  symbolt *symbol_ptr;

  do
  {
    new_symbol.base_name=
      basename_prefix+
      "$"+
      std::to_string(++temporary_counter);
    if(name_prefix.empty())
      new_symbol.name=new_symbol.base_name;
    else
      new_symbol.name=
        name_prefix+
        "::"+
        id2string(new_symbol.base_name);
    new_symbol.type=type;
    new_symbol.location=source_location;
    new_symbol.mode=symbol_mode;
  }
  while(symbol_table.move(new_symbol, symbol_ptr));

  return *symbol_ptr;
}
