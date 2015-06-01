/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>
#include <set>

#include <util/prefix.h>
#include <util/std_types.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/expr_util.h>
#include <util/config.h>
#include <util/cprover_prefix.h>

#include <linking/entry_point.h>
#include <goto-programs/goto_functions.h>

#include "java_entry_point.h"

//#include "zero_initializer.h"

#define INITIALIZE CPROVER_PREFIX "initialize"

/*******************************************************************\

Function: create_initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

namespace {

void create_initialize(symbol_tablet &symbol_table)
{
  symbolt initialize;
  initialize.name=INITIALIZE;
  initialize.base_name=INITIALIZE;
  initialize.mode=ID_java;

  code_typet type;
  type.return_type()=empty_typet();
  initialize.type=type;
  
  code_blockt init_code;
  
  namespacet ns(symbol_table);
  
  symbol_exprt rounding_mode=
    ns.lookup(CPROVER_PREFIX "rounding_mode").symbol_expr();

  init_code.add(code_assignt(rounding_mode, gen_zero(rounding_mode.type())));
  
  initialize.value=init_code;
  
  if(symbol_table.add(initialize))
    throw "failed to add "+std::string(INITIALIZE);
}

exprt gen_argument(const typet &type)
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

}

/*******************************************************************\

Function: java_static_lifetime_init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_static_lifetime_init(
  symbol_tablet &symbol_table,
  const source_locationt &source_location,
  message_handlert &message_handler)
{
  symbolt &initialize_symbol=symbol_table.lookup(INITIALIZE);
  code_blockt &code_block=to_code_block(to_code(initialize_symbol.value));
  
  // we need to zero out all static variables
  
  for(symbol_tablet::symbolst::const_iterator
      it=symbol_table.symbols.begin();
      it!=symbol_table.symbols.end();
      it++)
  {
    if(it->second.type.id()!=ID_code &&
       it->second.is_lvalue &&
       it->second.is_state_var &&
       it->second.is_static_lifetime &&
       it->second.value.is_not_nil() &&
       it->second.mode==ID_java)
    {
      code_assignt assignment(it->second.symbol_expr(), it->second.value);
      code_block.add(assignment);
    }
  }
  
  // we now need to run all the <clinit> methods

  for(symbol_tablet::symbolst::const_iterator
      it=symbol_table.symbols.begin();
      it!=symbol_table.symbols.end();
      it++)
  {
    if(it->second.base_name=="<clinit>" &&
       it->second.type.id()==ID_code &&
       it->second.mode==ID_java)
    {
      code_function_callt function_call;
      function_call.lhs()=nil_exprt();
      function_call.function()=it->second.symbol_expr();
      code_block.add(function_call);
    }
  }
  
  return false;
}

/*******************************************************************\

Function: java_entry_point

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_entry_point(
  symbol_tablet &symbol_table,
  const irep_idt &main_class,
  message_handlert &message_handler)
{
  // check if the entry point is already there
  if(symbol_table.symbols.find(goto_functionst::entry_point())!=
     symbol_table.symbols.end())
    return false; // silently ignore

  std::string entry_method;

  // are we given a function?
  if(config.main.empty())
  {
    // use main class
    entry_method=id2string(main_class)+".main";
  }
  else
    entry_method=id2string(config.main);

  std::string prefix="java::"+entry_method+":";

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

  create_initialize(symbol_table);

  if(java_static_lifetime_init(symbol_table, symbol.location, message_handler))
    return true;

  code_blockt init_code;

  // build call to initialization function
  {
    symbol_tablet::symbolst::iterator init_it=
      symbol_table.symbols.find("__CPROVER_initialize");

    if(init_it==symbol_table.symbols.end())
      throw "failed to find __CPROVER_initialize symbol";

    code_function_callt call_init;
    call_init.lhs().make_nil();
    call_init.add_source_location() = symbol.location;
    call_init.function()=init_it->second.symbol_expr();

    init_code.move_to_operands(call_init);
  }

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
  new_symbol.mode=ID_java;

  if(symbol_table.move(new_symbol))
  {
    messaget message;
    message.set_message_handler(message_handler);
    message.error() << "failed to move main symbol" << messaget::eom;
    return true;
  }

  return false;
}
