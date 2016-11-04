/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>
#include <set>
#include <iostream>

#include <util/prefix.h>
#include <util/std_types.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/expr_util.h>
#include <util/cprover_prefix.h>
#include <util/message.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/prefix.h>
#include <ansi-c/c_types.h>
#include <ansi-c/string_constant.h>

#include <goto-programs/goto_functions.h>

#include "java_entry_point.h"
#include "java_object_factory.h"

#define INITIALIZE CPROVER_PREFIX "initialize"

/*******************************************************************\

Function: create_initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void create_initialize(symbol_tablet &symbol_table)
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
      function_call.add_source_location()=source_location;
      code_block.add(function_call);
    }
  }

  return false;
}


/*******************************************************************\

Function: java_build_arguments

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt::operandst java_build_arguments(
  const symbolt &function,
  code_blockt &init_code,
  symbol_tablet &symbol_table)
{
  const code_typet::parameterst &parameters=
    to_code_type(function.type).parameters();

  exprt::operandst main_arguments;
  main_arguments.resize(parameters.size());

  for(std::size_t param_number=0;
      param_number<parameters.size();
      param_number++)
  {
    bool is_this=param_number==0 &&
                 parameters[param_number].get_this();
    bool allow_null=config.main!="" && !is_this;

    main_arguments[param_number]=
      object_factory(parameters[param_number].type(),
                     init_code, allow_null, symbol_table);

    const symbolt &p_symbol=
      symbol_table.lookup(parameters[param_number].get_identifier());

    // record as an input
    codet input(ID_input);
    input.operands().resize(2);
    input.op0()=address_of_exprt(
      index_exprt(string_constantt(p_symbol.base_name),
                  gen_zero(index_type())));
    input.op1()=main_arguments[param_number];
    input.add_source_location()=function.location;

    init_code.move_to_operands(input);
  }

  return main_arguments;
}

/*******************************************************************\

Function: java_record_outputs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_record_outputs(
  const symbolt &function,
  const exprt::operandst &main_arguments,
  code_blockt &init_code,
  symbol_tablet &symbol_table)
{
  const code_typet::parameterst &parameters=
    to_code_type(function.type).parameters();

  exprt::operandst result;
  result.reserve(parameters.size()+1);

  bool has_return_value=
    to_code_type(function.type).return_type()!=empty_typet();

  if(has_return_value)
  {
    // record return value
    codet output(ID_output);
    output.operands().resize(2);

    const symbolt &return_symbol=symbol_table.lookup("return'");

    output.op0()=address_of_exprt(
      index_exprt(string_constantt(return_symbol.base_name),
                  gen_zero(index_type())));
    output.op1()=return_symbol.symbol_expr();
    output.add_source_location()=function.location;

    init_code.move_to_operands(output);
  }

  for(std::size_t param_number=0;
      param_number<parameters.size();
      param_number++)
  {
    const symbolt &p_symbol=
      symbol_table.lookup(parameters[param_number].get_identifier());

    if(p_symbol.type.id()==ID_pointer)
    {
      // record as an output
      codet output(ID_output);
      output.operands().resize(2);
      output.op0()=address_of_exprt(
        index_exprt(string_constantt(p_symbol.base_name),
                    gen_zero(index_type())));
      output.op1()=main_arguments[param_number];
      output.add_source_location()=function.location;

      init_code.move_to_operands(output);
    }
  }
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

  messaget message(message_handler);

  symbolt symbol; // main function symbol

  // find main symbol
  if(config.main!="")
  {
    // Add java:: prefix
    std::string main_identifier="java::"+config.main;

    symbol_tablet::symbolst::const_iterator s_it;

    // Does it have a type signature? (':' suffix)
    if(config.main.rfind(':')==std::string::npos)
    {
      std::string prefix=main_identifier+':';
      std::set<irep_idt> matches;

      for(const auto &s : symbol_table.symbols)
        if(has_prefix(id2string(s.first), prefix) &&
           s.second.type.id()==ID_code)
          matches.insert(s.first);

      if(matches.empty())
      {
        message.error() << "main symbol `" << config.main
                        << "' not found" << messaget::eom;
        return true;
      }
      else if(matches.size()==1)
      {
        s_it=symbol_table.symbols.find(*matches.begin());
        assert(s_it!=symbol_table.symbols.end());
      }
      else
      {
        message.error() << "main symbol `" << config.main
                        << "' is ambiguous:\n";

        for(const auto &s : matches)
          message.error() << "  " << s << '\n';

        message.error() << messaget::eom;

        return true;
      }
    }
    else
    {
      // just look it up
      s_it=symbol_table.symbols.find(main_identifier);

      if(s_it==symbol_table.symbols.end())
      {
        message.error() << "main symbol `" << config.main
                        << "' not found" << messaget::eom;
        return true;
      }
    }

    // function symbol
    symbol=s_it->second;

    if(symbol.type.id()!=ID_code)
    {
      message.error() << "main symbol `" << config.main
                      << "' not a function" << messaget::eom;
      return true;
    }

    // check if it has a body
    if(symbol.value.is_nil())
    {
      message.error() << "main method `" << main_class
                      << "' has no body" << messaget::eom;
      return true;
    }
  }
  else
  {
    // no function given, we look for the main class
    assert(config.main=="");

    // are we given a main class?
    if(main_class.empty())
      return false; // silently ignore

    std::string entry_method=
      id2string(main_class)+".main";

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
      // Not found, silently ignore
      return false;
    }

    if(matches.size()>=2)
    {
      message.error() << "main method in `" << main_class
                      << "' is ambiguous" << messaget::eom;
      return true; // give up with error, no main
    }

    // function symbol
    symbol=symbol_table.symbols.find(*matches.begin())->second;

    // check if it has a body
    if(symbol.value.is_nil())
    {
      message.error() << "main method `" << main_class
                      << "' has no body" << messaget::eom;
      return true; // give up with error
    }
  }

  assert(!symbol.value.is_nil());
  assert(symbol.type.id()==ID_code);

  create_initialize(symbol_table);

  if(java_static_lifetime_init(symbol_table, symbol.location, message_handler))
    return true;

  code_blockt init_code;

  // build call to initialization function
  {
    symbol_tablet::symbolst::iterator init_it=
      symbol_table.symbols.find(INITIALIZE);

    if(init_it==symbol_table.symbols.end())
    {
      message.error() << "failed to find " INITIALIZE " symbol"
                      << messaget::eom;
      return true; // give up with error
    }

    code_function_callt call_init;
    call_init.lhs().make_nil();
    call_init.add_source_location()=symbol.location;
    call_init.function()=init_it->second.symbol_expr();

    init_code.move_to_operands(call_init);
  }

  // build call to the main method

  code_function_callt call_main;

  source_locationt loc = symbol.location;
  loc.set_function(symbol.name);
  source_locationt &dloc = loc;

  call_main.add_source_location()=dloc;
  call_main.function()=symbol.symbol_expr();
  call_main.function().add_source_location()=dloc;

  if(to_code_type(symbol.type).return_type()!=empty_typet())
  {
    auxiliary_symbolt return_symbol;
    return_symbol.mode=ID_C;
    return_symbol.is_static_lifetime=false;
    return_symbol.name="return'";
    return_symbol.base_name="return";
    return_symbol.type=to_code_type(symbol.type).return_type();

    symbol_table.add(return_symbol);
    call_main.lhs()=return_symbol.symbol_expr();
  }

  exprt::operandst main_arguments=
    java_build_arguments(symbol, init_code, symbol_table);
  call_main.arguments()=main_arguments;

  init_code.move_to_operands(call_main);

  java_record_outputs(symbol, main_arguments, init_code, symbol_table);

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
    message.error() << "failed to move main symbol" << messaget::eom;
    return true;
  }

  return false;
}
