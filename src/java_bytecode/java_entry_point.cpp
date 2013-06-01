/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#if 0
#include <cassert>
#include <cstdlib>

#include <util/namespace.h>
#include <util/expr_util.h>
#include <util/arith_tools.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>
#endif

#include <util/std_types.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/expr_util.h>
#include <util/config.h>

#include "java_entry_point.h"
//#include "zero_initializer.h"

/*******************************************************************\

Function: java_entry_point

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_entry_point(
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  // check if main is already there
  if(symbol_table.symbols.find(ID_main)!=symbol_table.symbols.end())
    return false; // silently ignore

  // are we given anything?
  
  if(config.main=="")
    return false; // no, give up silently

  irep_idt main_symbol="java::"+id2string(config.main);
  
  // look it up
  symbol_tablet::symbolst::const_iterator s_it=
    symbol_table.symbols.find(main_symbol);
  
  if(s_it==symbol_table.symbols.end())
  {
    messaget message(message_handler);
    message.error("main method `"+id2string(main_symbol)+"' not in symbol table");
    return true; // give up with error, no main
  }
    
  const symbolt &symbol=s_it->second;
  
  // check if it has a body
  if(symbol.value.is_nil())
  {
    messaget message(message_handler);
    message.error("main method `"+id2string(main_symbol)+"' has no body");
    return true; // give up with error
  }

  #if 0
  if(static_lifetime_init(symbol_table, symbol.location, message_handler))
    return true;
  #endif
  
  code_blockt init_code;
  
  // build call to initialization function

  #if 0
  {
    symbol_tablet::symbolst::iterator init_it=
      symbol_table.symbols.find("c::__CPROVER_initialize");

    if(init_it==symbol_table.symbols.end())
      throw "failed to find __CPROVER_initialize symbol";
  
    code_function_callt call_init;
    call_init.lhs().make_nil();
    call_init.location()=symbol.location;
    call_init.function()=symbol_expr(init_it->second);

    init_code.move_to_operands(call_init);
  }
  #endif

  // build call to main method
  
  code_function_callt call_main;
  call_main.location()=symbol.location;
  call_main.function()=symbol_expr(symbol);

  const code_typet::argumentst &arguments=
    to_code_type(symbol.type).arguments();

  exprt::operandst main_arguments;
  main_arguments.resize(arguments.size());

  for(unsigned i=0; i<arguments.size(); i++)
    main_arguments[i]=side_effect_expr_nondett(arguments[i].type());
  
  call_main.arguments()=main_arguments;

  init_code.move_to_operands(call_main);

  // add "main"
  symbolt new_symbol;

  code_typet main_type;
  main_type.return_type()=empty_typet();
  
  new_symbol.name=ID_main;
  new_symbol.type.swap(main_type);
  new_symbol.value.swap(init_code);
  
  if(symbol_table.move(new_symbol))
  {
    messaget message;
    message.set_message_handler(message_handler);
    message.error("failed to move main symbol");
    return true;
  }
  
  return false;
}
