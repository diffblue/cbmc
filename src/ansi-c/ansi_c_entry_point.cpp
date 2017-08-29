/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include <cassert>
#include <cstdlib>

#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/std_code.h>
#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>

#include <util/c_types.h>
#include <ansi-c/string_constant.h>

#include <goto-programs/goto_functions.h>
#include <langapi/wrap_entry_point.h>
#include <linking/static_lifetime_init.h>

#include "ansi_c_entry_point.h"
#include "ansi_c_language.h"
#include "c_nondet_symbol_factory.h"

exprt::operandst build_function_environment(
  const code_typet::parameterst &parameters,
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  exprt::operandst main_arguments;
  main_arguments.resize(parameters.size());

  for(std::size_t param_number=0;
      param_number<parameters.size();
      param_number++)
  {
    const code_typet::parametert &p=parameters[param_number];
    const irep_idt base_name=p.get_base_name().empty()?
      ("argument#"+std::to_string(param_number)):p.get_base_name();

    main_arguments[param_number]=
      c_nondet_symbol_factory(
        init_code,
        symbol_table,
        base_name,
        p.type(),
        p.source_location(),
        true);
  }

  return main_arguments;
}

void record_function_outputs(
  const symbolt &function,
  code_blockt &init_code,
  symbol_tablet &symbol_table)
{
  bool has_return_value=
    to_code_type(function.type).return_type()!=empty_typet();

  if(has_return_value)
  {
    // record return value
    codet output(ID_output);
    output.operands().resize(2);

    const symbolt &return_symbol=symbol_table.lookup("return'");

    output.op0()=
      address_of_exprt(
        index_exprt(
          string_constantt(return_symbol.base_name),
          from_integer(0, index_type())));

    output.op1()=return_symbol.symbol_expr();
    output.add_source_location()=function.location;

    init_code.move_to_operands(output);
  }

  #if 0
  std::size_t i=0;

  for(const auto &p : parameters)
  {
    if(p.get_identifier().empty())
      continue;

    irep_idt identifier=p.get_identifier();

    const symbolt &symbol=symbol_table.lookup(identifier);

    if(symbol.type.id()==ID_pointer)
    {
      codet output(ID_output);
      output.operands().resize(2);

      output.op0()=
        address_of_exprt(
          index_exprt(
            string_constantt(symbol.base_name),
            from_integer(0, index_type())));
      output.op1()=symbol.symbol_expr();
      output.add_source_location()=p.source_location();

      init_code.move_to_operands(output);
    }

    i++;
  }
  #endif
}

bool ansi_c_entry_point(
  symbol_tablet &symbol_table,
  const std::string &standard_main,
  message_handlert &message_handler,
  bool wrap_entry_point)
{
  // check if entry point is already there
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
    main_symbol=standard_main;

  // look it up
  symbol_tablet::symbolst::const_iterator s_it=
    symbol_table.symbols.find(main_symbol);

  if(s_it==symbol_table.symbols.end())
    return false; // give up silently

  const symbolt &symbol=s_it->second;

  // check if it has a body
  if(symbol.value.is_nil())
  {
    messaget message(message_handler);
    message.error() << "main symbol `" << id2string(main_symbol)
                    << "' has no body" << messaget::eom;
    return false; // give up
  }

  if(static_lifetime_init(symbol_table, symbol.location, message_handler))
    return true;

  code_blockt init_code;

  // build call to initialization function

  {
    symbol_tablet::symbolst::iterator init_it=
      symbol_table.symbols.find(INITIALIZE_FUNCTION);

    if(init_it==symbol_table.symbols.end())
    {
      messaget message(message_handler);
      message.error() << "failed to find " CPROVER_PREFIX "initialize symbol"
                      << messaget::eom;
      return true;
    }

    code_function_callt call_init;
    call_init.lhs().make_nil();
    call_init.add_source_location()=symbol.location;
    call_init.function()=init_it->second.symbol_expr();

    init_code.move_to_operands(call_init);
  }

  // build call to main function

  code_function_callt call_main;
  call_main.add_source_location()=symbol.location;
  call_main.function()=symbol.symbol_expr();
  call_main.function().add_source_location()=symbol.location;

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

  const code_typet::parameterst &parameters=
    to_code_type(symbol.type).parameters();

  if(symbol.name==standard_main)
  {
    if(parameters.empty())
    {
      // ok
    }
    else if(parameters.size()==2 || parameters.size()==3)
    {
      namespacet ns(symbol_table);

      const symbolt &argc_symbol=ns.lookup("argc'");
      const symbolt &argv_symbol=ns.lookup("argv'");

      {
        // assume argc is at least one
        exprt one=from_integer(1, argc_symbol.type);

        exprt ge(ID_ge, typet(ID_bool));
        ge.copy_to_operands(argc_symbol.symbol_expr(), one);

        codet assumption;
        assumption.set_statement(ID_assume);
        assumption.move_to_operands(ge);
        init_code.move_to_operands(assumption);
      }

      {
        // assume argc is at most MAX/8-1
        mp_integer upper_bound=
          power(2, config.ansi_c.int_width-4);

        exprt bound_expr=from_integer(upper_bound, argc_symbol.type);

        exprt le(ID_le, typet(ID_bool));
        le.copy_to_operands(argc_symbol.symbol_expr(), bound_expr);

        codet assumption;
        assumption.set_statement(ID_assume);
        assumption.move_to_operands(le);
        init_code.move_to_operands(assumption);
      }

      {
        // record argc as an input
        codet input(ID_input);
        input.operands().resize(2);
        input.op0()=address_of_exprt(
          index_exprt(string_constantt("argc"), from_integer(0, index_type())));
        input.op1()=argc_symbol.symbol_expr();
        init_code.move_to_operands(input);
      }

      if(parameters.size()==3)
      {
        const symbolt &envp_size_symbol=ns.lookup("envp_size'");

        // assume envp_size is INTMAX-1
        mp_integer max;

        if(envp_size_symbol.type.id()==ID_signedbv)
        {
          max=to_signedbv_type(envp_size_symbol.type).largest();
        }
        else if(envp_size_symbol.type.id()==ID_unsignedbv)
        {
          max=to_unsignedbv_type(envp_size_symbol.type).largest();
        }
        else
          assert(false);

        exprt max_minus_one=from_integer(max-1, envp_size_symbol.type);

        exprt le(ID_le, bool_typet());
        le.copy_to_operands(envp_size_symbol.symbol_expr(), max_minus_one);

        codet assumption;
        assumption.set_statement(ID_assume);
        assumption.move_to_operands(le);
        init_code.move_to_operands(assumption);
      }

      {
        /* zero_string doesn't work yet */

        /*
        exprt zero_string(ID_zero_string, array_typet());
        zero_string.type().subtype()=char_type();
        zero_string.type().set(ID_size, "infinity");
        exprt index(ID_index, char_type());
        index.copy_to_operands(zero_string, from_integer(0, uint_type()));
        exprt address_of("address_of", pointer_typet());
        address_of.type().subtype()=char_type();
        address_of.copy_to_operands(index);

        if(argv_symbol.type.subtype()!=address_of.type())
          address_of.make_typecast(argv_symbol.type.subtype());

        // assign argv[*] to the address of a string-object
        exprt array_of("array_of", argv_symbol.type);
        array_of.copy_to_operands(address_of);

        init_code.copy_to_operands(
          code_assignt(argv_symbol.symbol_expr(), array_of));
        */
      }

      {
        // assign argv[argc] to NULL
        exprt null(ID_constant, argv_symbol.type.subtype());
        null.set(ID_value, ID_NULL);

        exprt index_expr(ID_index, argv_symbol.type.subtype());
        index_expr.copy_to_operands(
          argv_symbol.symbol_expr(),
          argc_symbol.symbol_expr());

        // disable bounds check on that one
        index_expr.set("bounds_check", false);

        init_code.copy_to_operands(code_assignt(index_expr, null));
      }

      if(parameters.size()==3)
      {
        const symbolt &envp_symbol=ns.lookup("envp'");
        const symbolt &envp_size_symbol=ns.lookup("envp_size'");

        // assume envp[envp_size] is NULL
        exprt null(ID_constant, envp_symbol.type.subtype());
        null.set(ID_value, ID_NULL);

        exprt index_expr(ID_index, envp_symbol.type.subtype());
        index_expr.copy_to_operands(
          envp_symbol.symbol_expr(),
          envp_size_symbol.symbol_expr());

        // disable bounds check on that one
        index_expr.set("bounds_check", false);

        exprt is_null(ID_equal, typet(ID_bool));
        is_null.copy_to_operands(index_expr, null);

        codet assumption2;
        assumption2.set_statement(ID_assume);
        assumption2.move_to_operands(is_null);
        init_code.move_to_operands(assumption2);
      }

      {
        exprt::operandst &operands=call_main.arguments();

        if(parameters.size()==3)
          operands.resize(3);
        else
          operands.resize(2);

        exprt &op0=operands[0];
        exprt &op1=operands[1];

        op0=argc_symbol.symbol_expr();

        {
          const exprt &arg1=parameters[1];

          exprt index_expr(ID_index, arg1.type().subtype());
          index_expr.copy_to_operands(
            argv_symbol.symbol_expr(),
            from_integer(0, index_type()));

          // disable bounds check on that one
          index_expr.set("bounds_check", false);

          op1=exprt(ID_address_of, arg1.type());
          op1.move_to_operands(index_expr);
        }

        // do we need envp?
        if(parameters.size()==3)
        {
          const symbolt &envp_symbol=ns.lookup("envp'");
          exprt &op2=operands[2];

          const exprt &arg2=parameters[2];

          exprt index_expr(ID_index, arg2.type().subtype());
          index_expr.copy_to_operands(
            envp_symbol.symbol_expr(), from_integer(0, index_type()));

          op2=exprt(ID_address_of, arg2.type());
          op2.move_to_operands(index_expr);
        }
      }
    }
    else
      assert(false);
  }
  else
  {
    // produce nondet arguments
    call_main.arguments()=
      build_function_environment(
        parameters,
        init_code,
        symbol_table,
        message_handler);
  }

  if (wrap_entry_point) {
    auto wrapped_main = wrap_entry_point_in_while(call_main);
    init_code.move_to_operands(wrapped_main);
  } else {
    init_code.move_to_operands(call_main);
  }

  // TODO: add read/modified (recursively in call graph) globals as INPUT/OUTPUT

  record_function_outputs(symbol, init_code, symbol_table);

  // add the entry point symbol
  symbolt new_symbol;

  code_typet main_type;
  main_type.return_type()=empty_typet();

  new_symbol.name=goto_functionst::entry_point();
  new_symbol.type.swap(main_type);
  new_symbol.value.swap(init_code);
  new_symbol.mode=symbol.mode;

  if(symbol_table.move(new_symbol))
  {
    messaget message;
    message.set_message_handler(message_handler);
    message.error() << "failed to move main symbol" << messaget::eom;
    return true;
  }

  return false;
}
