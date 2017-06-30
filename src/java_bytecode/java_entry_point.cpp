/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_entry_point.h"

#include <algorithm>
#include <set>
#include <iostream>

#include <util/arith_tools.h>
#include <util/prefix.h>
#include <util/std_types.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/cprover_prefix.h>
#include <util/message.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/suffix.h>

#include <util/c_types.h>
#include <ansi-c/string_constant.h>

#include <goto-programs/remove_exceptions.h>

#include "java_object_factory.h"
#include "java_types.h"

#define INITIALIZE CPROVER_PREFIX "initialize"

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

  init_code.add(
    code_assignt(rounding_mode, from_integer(0, rounding_mode.type())));

  initialize.value=init_code;

  if(symbol_table.add(initialize))
    throw "failed to add "+std::string(INITIALIZE);
}


static bool should_init_symbol(const symbolt &sym)
{
  if(sym.type.id()!=ID_code &&
     sym.is_lvalue &&
     sym.is_state_var &&
     sym.is_static_lifetime &&
     sym.mode==ID_java)
    return true;

  return has_prefix(id2string(sym.name), "java::java.lang.String.Literal");
}

void java_static_lifetime_init(
  symbol_tablet &symbol_table,
  const source_locationt &source_location,
  bool assume_init_pointers_not_null,
  unsigned max_nondet_array_length)
{
  symbolt &initialize_symbol=symbol_table.lookup(INITIALIZE);
  code_blockt &code_block=to_code_block(to_code(initialize_symbol.value));

  // We need to zero out all static variables, or nondet-initialize if they're
  // external. Iterate over a copy of the symtab, as its iterators are
  // invalidated by object_factory:

  std::list<irep_idt> symbol_names;
  for(const auto &entry : symbol_table.symbols)
    symbol_names.push_back(entry.first);

  for(const auto &symname : symbol_names)
  {
    const symbolt &sym=symbol_table.lookup(symname);
    if(should_init_symbol(sym))
    {
      if(sym.value.is_nil() && sym.type!=empty_typet())
      {
        bool allow_null=!assume_init_pointers_not_null;
        if(allow_null)
        {
          std::string namestr=id2string(sym.symbol_expr().get_identifier());
          const std::string suffix="@class_model";
          // Static '.class' fields are always non-null.
          if(has_suffix(namestr, suffix))
            allow_null=false;
          if(allow_null && has_prefix(
               namestr,
               "java::java.lang.String.Literal"))
            allow_null=false;
        }
        auto newsym=object_factory(
          sym.type,
          symname,
          code_block,
          allow_null,
          symbol_table,
          max_nondet_array_length,
          source_location);
        code_assignt assignment(sym.symbol_expr(), newsym);
        code_block.add(assignment);
      }
      else if(sym.value.is_not_nil())
      {
        code_assignt assignment(sym.symbol_expr(), sym.value);
        assignment.add_source_location()=source_location;
        code_block.add(assignment);
      }
    }
  }
}

exprt::operandst java_build_arguments(
  const symbolt &function,
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  bool assume_init_pointers_not_null,
  unsigned max_nondet_array_length)
{
  const code_typet::parameterst &parameters=
    to_code_type(function.type).parameters();

  exprt::operandst main_arguments;
  main_arguments.resize(parameters.size());

  for(std::size_t param_number=0;
      param_number<parameters.size();
      param_number++)
  {
    bool is_this=(param_number==0) &&
                 parameters[param_number].get_this();
    bool is_default_entry_point(config.main.empty());
    bool is_main=is_default_entry_point;
    if(!is_main)
    {
      bool named_main=has_suffix(config.main, ".main");
      const typet &string_array_type=
        java_type_from_string("[Ljava.lang.String;");
      bool has_correct_type=
        to_code_type(function.type).return_type().id()==ID_empty &&
        (!to_code_type(function.type).has_this()) &&
        parameters.size()==1 &&
        parameters[0].type().full_eq(string_array_type);
      is_main=(named_main && has_correct_type);
    }

    const code_typet::parametert &p=parameters[param_number];
    const irep_idt base_name=p.get_base_name().empty()?
      ("argument#"+std::to_string(param_number)):p.get_base_name();

    bool allow_null=(!is_main) && (!is_this) && !assume_init_pointers_not_null;

    main_arguments[param_number]=
      object_factory(
        p.type(),
        base_name,
        init_code,
        allow_null,
        symbol_table,
        max_nondet_array_length,
        function.location);

    // record as an input
    codet input(ID_input);
    input.operands().resize(2);
    input.op0()=
      address_of_exprt(
        index_exprt(
          string_constantt(base_name),
          from_integer(0, index_type())));
    input.op1()=main_arguments[param_number];
    input.add_source_location()=function.location;

    init_code.move_to_operands(input);
  }

  return main_arguments;
}

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

    const symbolt &return_symbol=
      symbol_table.lookup(JAVA_ENTRY_POINT_RETURN_SYMBOL);

    output.op0()=
      address_of_exprt(
        index_exprt(
          string_constantt(return_symbol.base_name),
          from_integer(0, index_type())));
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
      output.op0()=
        address_of_exprt(
          index_exprt(
            string_constantt(p_symbol.base_name),
            from_integer(0, index_type())));
      output.op1()=main_arguments[param_number];
      output.add_source_location()=function.location;

      init_code.move_to_operands(output);
    }
  }

  // record exceptional return variable as output
  codet output(ID_output);
  output.operands().resize(2);

  assert(symbol_table.has_symbol(id2string(function.name)+EXC_SUFFIX));

  // retrieve the exception variable
  const symbolt exc_symbol=symbol_table.lookup(
    id2string(function.name)+EXC_SUFFIX);

  output.op0()=address_of_exprt(
    index_exprt(string_constantt(exc_symbol.base_name),
                from_integer(0, index_type())));
  output.op1()=exc_symbol.symbol_expr();
  output.add_source_location()=function.location;

  init_code.move_to_operands(output);
}

main_function_resultt get_main_symbol(
  symbol_tablet &symbol_table,
  const irep_idt &main_class,
  message_handlert &message_handler,
  bool allow_no_body)
{
  symbolt symbol;
  main_function_resultt res;

  messaget message(message_handler);

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
        res.main_function=symbol;
        res.error_found=true;
        res.stop_convert=true;
        return res;
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
        res.main_function=symbol;
        res.error_found=true;
        res.stop_convert=true;
        return res;
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
        res.main_function=symbol;
        res.error_found=true;
        res.stop_convert=true;
        return res;
      }
    }
    // function symbol
    symbol=s_it->second;

    if(symbol.type.id()!=ID_code)
    {
      message.error() << "main symbol `" << config.main
                      << "' not a function" << messaget::eom;
      res.main_function=symbol;
      res.error_found=true;
      res.stop_convert=true;
      return res;
    }

    // check if it has a body
    if(symbol.value.is_nil() && !allow_no_body)
    {
      message.error() << "main method `" << main_class
                      << "' has no body" << messaget::eom;
      res.main_function=symbol;
      res.error_found=true;
      res.stop_convert=true;
      return res;
    }
  }
  else
  {
    // no function given, we look for the main class
    assert(config.main=="");

    // are we given a main class?
    if(main_class.empty())
    {
      res.main_function=symbol;
      res.error_found=false;
      res.stop_convert=true;
      return res; // silently ignore
    }

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
      res.main_function=symbol;
      res.error_found=false;
      res.stop_convert=true;
      return res;
    }

    if(matches.size()>=2)
    {
      message.error() << "main method in `" << main_class
                      << "' is ambiguous" << messaget::eom;
      res.main_function=symbolt();
      res.error_found=true;
      res.stop_convert=true;
      return res;  // give up with error, no main
    }

    // function symbol
    symbol=symbol_table.symbols.find(*matches.begin())->second;

    // check if it has a body
    if(symbol.value.is_nil() && !allow_no_body)
    {
      message.error() << "main method `" << main_class
                      << "' has no body" << messaget::eom;
      res.main_function=symbol;
      res.error_found=true;
      res.stop_convert=true;
      return res;  // give up with error
    }
  }

  res.main_function=symbol;
  res.error_found=false;
  res.stop_convert=false;
  return res;  // give up with error
}

/// find entry point and create initialization code for function
/// symbol_table
/// main class
/// message_handler
/// \param assume_init_pointers_not_null: allow pointers in initialization code
///   to be null
/// max_nondet_array_length
/// \return true if error occurred on entry point search
bool java_entry_point(
  symbol_tablet &symbol_table,
  const irep_idt &main_class,
  message_handlert &message_handler,
  bool assume_init_pointers_not_null,
  size_t max_nondet_array_length)
{
  // check if the entry point is already there
  if(symbol_table.symbols.find(goto_functionst::entry_point())!=
     symbol_table.symbols.end())
    return false; // silently ignore

  messaget message(message_handler);
  main_function_resultt res=
    get_main_symbol(symbol_table, main_class, message_handler);
  if(res.stop_convert)
    return res.stop_convert;
  symbolt symbol=res.main_function;

  assert(!symbol.value.is_nil());
  assert(symbol.type.id()==ID_code);

  create_initialize(symbol_table);

  java_static_lifetime_init(
    symbol_table,
    symbol.location,
    assume_init_pointers_not_null,
    max_nondet_array_length);

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

  source_locationt loc=symbol.location;
  loc.set_function(symbol.name);
  source_locationt &dloc=loc;

  call_main.add_source_location()=dloc;
  call_main.function()=symbol.symbol_expr();
  call_main.function().add_source_location()=dloc;

  if(to_code_type(symbol.type).return_type()!=empty_typet())
  {
    auxiliary_symbolt return_symbol;
    return_symbol.mode=ID_java;
    return_symbol.is_static_lifetime=false;
    return_symbol.name=JAVA_ENTRY_POINT_RETURN_SYMBOL;
    return_symbol.base_name="return";
    return_symbol.type=to_code_type(symbol.type).return_type();

    symbol_table.add(return_symbol);
    call_main.lhs()=return_symbol.symbol_expr();
  }

  if(!symbol_table.has_symbol(id2string(symbol.name)+EXC_SUFFIX))
  {
    // add the exceptional return value
    auxiliary_symbolt exc_symbol;
    exc_symbol.mode=ID_java;
    exc_symbol.is_static_lifetime=true;
    exc_symbol.name=id2string(symbol.name)+EXC_SUFFIX;
    exc_symbol.base_name=id2string(symbol.name)+EXC_SUFFIX;
    exc_symbol.type=java_reference_type(empty_typet());
    symbol_table.add(exc_symbol);
  }

  exprt::operandst main_arguments=
    java_build_arguments(
      symbol,
      init_code,
      symbol_table,
      assume_init_pointers_not_null,
      max_nondet_array_length);
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
