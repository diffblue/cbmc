/*******************************************************************\

Module: Find module symbol using name

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Find module symbol using name

#include "get_module.h"

#include <list>
#include <set>

#include "message.h"
#include "symbol_table.h"

typedef std::list<const symbolt *> symbolptr_listt;

#define forall_symbolptr_list(it, list) \
  for(symbolptr_listt::const_iterator it=(list).begin(); \
      it!=(list).end(); ++it)

#define Forall_symbolptr_list(it, list) \
  for(symbolptr_listt::iterator it=(list).begin(); \
      it!=(list).end(); ++it)

const symbolt &get_module_by_name(
  const symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  symbolptr_listt symbolptr_list;
  messaget message(message_handler);

  forall_symbol_base_map(it, symbol_table.symbol_base_map, module)
  {
    symbol_tablet::symbolst::const_iterator it2=
      symbol_table.symbols.find(it->second);

    if(it2==symbol_table.symbols.end())
      continue;

    const symbolt &s=it2->second;

    if(s.is_type || s.type.id()!=ID_module)
      continue;

    symbolptr_list.push_back(&s);
  }

  if(symbolptr_list.empty())
  {
    message.error() << "module '" << module << "' not found" << messaget::eom;
    throw 0;
  }
  else if(symbolptr_list.size()>=2)
  {
    message.error() << "module '" << module << "' does not uniquely resolve:\n";

    forall_symbolptr_list(it, symbolptr_list)
      message.error() << "  " << (*it)->name << '\n';

    message.error() << messaget::eom;
    throw 0;
  }

  // symbolptr_list has exactly one element

  return *symbolptr_list.front();
}

const symbolt &get_module(
  const symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  if(!module.empty())
    return get_module_by_name(symbol_table, module, message_handler);

  symbolptr_listt symbolptr_list, main_symbolptr_list;
  messaget message(message_handler);

  for(const auto &symbol_pair : symbol_table.symbols)
  {
    const symbolt &s = symbol_pair.second;

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

    for(const auto &s_it : modules)
      message.error() << "  " << s_it << '\n';

    message.error() << messaget::eom;
    throw 0;
  }

  // symbolptr_list has exactly one element

  const symbolt &symbol=*symbolptr_list.front();

  message.status() << "Using module '" << symbol.pretty_name << "'"
                   << messaget::eom;

  return symbol;
}
