/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>

#include <util/prefix.h>
#include <util/std_types.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/expr_util.h>
#include <util/config.h>

#include <goto-programs/goto_functions.h>

#include "java_entry_point.h"
//#include "zero_initializer.h"

/*******************************************************************\

Function: gen_argument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static exprt gen_argument(const typet &type)
{
  if(type.id()==ID_pointer)
  {
    /*
    side_effect_exprt result(ID_java_new);
    result.operands().resize(1);
    return result;
    */
    return side_effect_expr_nondett(type);
  }
  else
    return side_effect_expr_nondett(type);
}

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
  // check if the entry point is already there
  if(symbol_table.symbols.find(goto_functionst::entry_point())!=
     symbol_table.symbols.end())
    return false; // silently ignore

  // are we given anything?
  
  if(config.main=="")
    return false; // no, give up silently

  std::string prefix="java::"+id2string(config.main)+":";
  
  // look it up
  std::set<irep_idt> matches;
  
  for(symbol_tablet::symbolst::const_iterator
      s_it=symbol_table.symbols.begin();
      s_it!=symbol_table.symbols.end();
      s_it++)
  {
    if(s_it->second.type.id()==ID_code &&
       has_prefix(id2string(s_it->first), prefix))
      matches.insert(s_it->first);
  }
  
  if(matches.empty())
  {
    messaget message(message_handler);
    message.error() << "main method `" << config.main
                    << "' not in symbol table" << messaget::eom;
    return true; // give up with error, no main
  }
    
  if(matches.size()>=2)
  {
    messaget message(message_handler);
    message.error() << "main method `" << config.main 
                    << "' is ambiguous" << messaget::eom;
    return true; // give up with error, no main
  }
  
  const symbolt &symbol=
    symbol_table.symbols.find(*matches.begin())->second;
  
  // check if it has a body
  if(symbol.value.is_nil())
  {
    messaget message(message_handler);
    message.error() << "main method `" << config.main 
                    << "' has no body" << messaget::eom;
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
      symbol_table.symbols.find("__CPROVER_initialize");

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
  call_main.add_source_location()=symbol.location;
  call_main.function()=symbol.symbol_expr();

  const code_typet::parameterst &parameters=
    to_code_type(symbol.type).parameters();

  exprt::operandst main_arguments;
  main_arguments.resize(parameters.size());

  for(unsigned i=0; i<parameters.size(); i++)
    main_arguments[i]=gen_argument(parameters[i].type());
  
  call_main.arguments()=main_arguments;

  init_code.move_to_operands(call_main);

  // add "main"
  symbolt new_symbol;

  code_typet main_type;
  main_type.return_type()=empty_typet();
  
  new_symbol.name=goto_functionst::entry_point();
  new_symbol.type.swap(main_type);
  new_symbol.value.swap(init_code);
  
  if(symbol_table.move(new_symbol))
  {
    messaget message;
    message.set_message_handler(message_handler);
    message.error() << "failed to move main symbol" << messaget::eom;
    return true;
  }
  
  return false;
}
