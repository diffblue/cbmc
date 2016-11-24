/*******************************************************************\

Module: Find module symbol using name

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>

#include "get_module.h"
#include "message.h"
#include "symbol_table.h"

/*******************************************************************\

Function: get_module_by_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const symbolt &get_module_by_name(
  const symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  symbolptr_listt symbolptr_list;
  messaget message(message_handler);

  forall_symbol_base_map(it, symbol_table.symbol_base_map, module)
  {
    symbol_tablet::symbolst::const_iterator it2=symbol_table.symbols.find(it->second);

    if(it2==symbol_table.symbols.end())
      continue;

    const symbolt &s=it2->second;

    if(s.is_type || s.type.id()!=ID_module)
      continue;
    
    symbolptr_list.push_back(&s);
  }

  if(symbolptr_list.empty())
  {
    message.error() << "module `" << module << "' not found" << messaget::eom;
    throw 0;
  }
  else if(symbolptr_list.size()>=2)
  {
    message.error() << "module `" << module << "' does not uniquely resolve:\n";

    forall_symbolptr_list(it, symbolptr_list)
      message.error() << "  " << (*it)->name << '\n';

    message.error() << messaget::eom;
    throw 0;
  }

  // symbolptr_list has exactly one element

  return *symbolptr_list.front();
}

/*******************************************************************\

Function: get_module

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const symbolt &get_module(
  const symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  if(module!="")
    return get_module_by_name(symbol_table, module, message_handler);

  symbolptr_listt symbolptr_list, main_symbolptr_list;
  messaget message(message_handler);

  forall_symbols(it, symbol_table.symbols)
  {
    const symbolt &s=it->second;
    
    if(s.type.id()!=ID_module)
      continue;

    // this is our default    
    if(s.base_name==ID_main)
      return get_module_by_name(symbol_table, "main", message_handler);
    
    symbolptr_list.push_back(&s);
  }

  if(symbolptr_list.empty())
  {
    message.error() << "no module found" << messaget::eom;
    throw 0;
  }
  else if(symbolptr_list.size()>=2)
  {
    // sorted alphabetically
    std::set<std::string> modules;

    forall_symbolptr_list(it, symbolptr_list)
      modules.insert(id2string((*it)->pretty_name));
  
    message.error() << "multiple modules found, please select one:\n";
    
    for(std::set<std::string>::const_iterator
        s_it=modules.begin(); s_it!=modules.end(); s_it++)
      message.error() << "  " << *s_it << '\n';

    message.error() << messaget::eom;
    throw 0;
  }

  // symbolptr_list has exactly one element
  
  const symbolt &symbol=*symbolptr_list.front();

  message.status() << "Using module `" << symbol.pretty_name << "'"
                   << messaget::eom;

  return symbol;
}

