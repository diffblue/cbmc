/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#include "jsil_entry_point.h"

#include <util/arith_tools.h>
#include <util/config.h>
#include <util/message.h>

#include <goto-programs/goto_functions.h>

#include <linking/static_lifetime_init.h>

static void create_initialize(symbol_tablet &symbol_table)
{
  symbolt initialize;
  initialize.name = INITIALIZE_FUNCTION;
  initialize.base_name = INITIALIZE_FUNCTION;
  initialize.mode="jsil";

  initialize.type = code_typet({}, empty_typet());

  code_blockt init_code;

  namespacet ns(symbol_table);

  symbol_exprt rounding_mode=
    ns.lookup(CPROVER_PREFIX "rounding_mode").symbol_expr();

  code_assignt a(rounding_mode, from_integer(0, rounding_mode.type()));
  init_code.add(a);

  initialize.value=init_code;

  if(symbol_table.add(initialize))
    throw "failed to add " INITIALIZE_FUNCTION;
}

bool jsil_entry_point(
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  // check if main is already there
  if(symbol_table.symbols.find(goto_functionst::entry_point())!=
     symbol_table.symbols.end())
    return false; // silently ignore

  irep_idt main_symbol;

  // find main symbol
  if(config.main!="")
  {
    std::list<irep_idt> matches;

    forall_symbol_base_map(it, symbol_table.symbol_base_map, config.main)
    {
      // look it up
      symbol_tablet::symbolst::const_iterator s_it=
        symbol_table.symbols.find(it->second);

      if(s_it==symbol_table.symbols.end())
        continue;

      if(s_it->second.type.id()==ID_code)
        matches.push_back(it->second);
    }

    if(matches.empty())
    {
      messaget message(message_handler);
      message.error() << "main symbol `" << config.main
                      << "' not found" << messaget::eom;
      return true; // give up
    }

    if(matches.size()>=2)
    {
      messaget message(message_handler);
      message.error() << "main symbol `" << config.main
                      << "' is ambiguous" << messaget::eom;
      return true;
    }

    main_symbol=matches.front();
  }
  else
    main_symbol=ID_main;

  // look it up
  symbol_tablet::symbolst::const_iterator s_it=
    symbol_table.symbols.find(main_symbol);

  if(s_it==symbol_table.symbols.end())
  {
    messaget message(message_handler);
    message.error() << "main symbol `" << id2string(main_symbol)
                    << "' not in symbol table" << messaget::eom;
    return true; // give up, no main
  }

  const symbolt &symbol=s_it->second;

  // check if it has a body
  if(symbol.value.is_nil())
  {
    messaget message(message_handler);
    message.error() << "main symbol `" << main_symbol
                    << "' has no body" << messaget::eom;
    return false; // give up
  }

  create_initialize(symbol_table);

  code_blockt init_code;

  // build call to initialization function

  {
    symbol_tablet::symbolst::const_iterator init_it=
      symbol_table.symbols.find(INITIALIZE_FUNCTION);

    if(init_it==symbol_table.symbols.end())
      throw "failed to find " INITIALIZE_FUNCTION " symbol";

    code_function_callt call_init(init_it->second.symbol_expr());
    call_init.add_source_location()=symbol.location;
    init_code.add(call_init);
  }

  // build call to main function

  code_function_callt call_main(symbol.symbol_expr());
  call_main.add_source_location()=symbol.location;
  call_main.function().add_source_location()=symbol.location;

  init_code.add(call_main);

  // add "main"
  symbolt new_symbol;

  new_symbol.name=goto_functionst::entry_point();
  new_symbol.type = code_typet({}, empty_typet());
  new_symbol.value.swap(init_code);

  if(!symbol_table.insert(std::move(new_symbol)).second)
  {
    messaget message;
    message.set_message_handler(message_handler);
    message.error() << "failed to move main symbol" << messaget::eom;
    return true;
  }

  return false;
}
