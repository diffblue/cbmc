/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <cstdlib>

#include <namespace.h>
#include <expr_util.h>
#include <std_expr.h>
#include <arith_tools.h>
#include <std_code.h>
#include <config.h>
#include <cprover_prefix.h>
#include <prefix.h>

#include <ansi-c/c_types.h>

#include "entry_point.h"
#include "zero_initializer.h"

/*******************************************************************\

Function: build_function_environment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt::operandst build_function_environment(
  const code_typet::argumentst &arguments)
{
  exprt::operandst result;
  result.resize(arguments.size());

  for(unsigned i=0; i<arguments.size(); i++)
  {
    result[i]=side_effect_expr_nondett(arguments[i].type());
  }
  
  return result;
}

/*******************************************************************\

Function: static_lifetime_init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool static_lifetime_init(
  contextt &context,
  const locationt &location,
  message_handlert &message_handler)
{
  contextt::symbolst::iterator s_it=
    context.symbols.find("c::__CPROVER_initialize");

  if(s_it==context.symbols.end()) return false;

  symbolt &init_symbol=s_it->second;
  
  init_symbol.value=code_blockt();
  init_symbol.value.location()=location;

  code_blockt &dest=to_code_block(to_code(init_symbol.value));
  
  // do assignments based on "value"

  forall_symbols(it, context.symbols)
  {
    const irep_idt &identifier=it->first;
  
    if(!it->second.static_lifetime) continue;

    if(it->second.is_type) continue;

    // special values
    if(identifier==CPROVER_PREFIX "constant_infinity_uint" ||
       identifier==CPROVER_PREFIX "memory" ||
       identifier=="c::__func__" ||
       identifier=="c::__FUNCTION__" ||
       identifier=="c::__PRETTY_FUNCTION__" ||
       identifier=="c::argc'" ||
       identifier=="c::argv'" ||
       identifier=="c::envp'" ||
       identifier=="c::envp_size'")
      continue;
      
    // just for linking
    if(has_prefix(id2string(identifier), CPROVER_PREFIX "architecture_"))
      continue;
      
    // just code
    if(it->second.type.id()==ID_code)
      continue;
      
    exprt rhs;
      
    if(it->second.value.is_nil())
    {
      try
      {
        namespacet ns(context);
        rhs=zero_initializer(it->second.type, it->second.location, ns, message_handler);
        assert(rhs.is_not_nil());
      }
      
      catch(...)
      {
        return true;
      }
    }
    else
      rhs=it->second.value;
    
    symbol_exprt symbol(it->second.name, it->second.type);
 
    code_assignt code(symbol, rhs);
    code.location()=it->second.location;

    dest.move_to_operands(code);
  }

  // call designated "initialization" functions

  forall_symbols(it, context.symbols)
  {
    if(it->second.type.get_bool("initialization") &&
       it->second.type.id()==ID_code)
    {
      code_function_callt function_call;      
      function_call.function()=symbol_expr(it->second);
      function_call.location()=location;
      dest.move_to_operands(function_call);
    }
  }

  return false;
}

/*******************************************************************\

Function: entry_point

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool entry_point(
  contextt &context,
  const std::string &standard_main,
  message_handlert &message_handler)
{
  // check if main is already there
  if(context.symbols.find(ID_main)!=context.symbols.end())
    return false; // silently ignore

  irep_idt main_symbol;
  
  // find main symbol
  if(config.main!="")
  {
    std::list<irep_idt> matches;
  
    forall_symbol_base_map(it, context.symbol_base_map, config.main)
    {
      // look it up
      contextt::symbolst::const_iterator s_it=context.symbols.find(it->second);
      
      if(s_it==context.symbols.end()) continue;
    
      if(s_it->second.type.id()==ID_code)
        matches.push_back(it->second);
    }
    
    if(matches.empty())
    {
      messaget message(message_handler);
      message.error("main symbol `"+config.main+"' not found");
      return true; // give up
    }
    
    if(matches.size()>=2)
    {
      messaget message(message_handler);
      message.error("main symbol `"+config.main+"' is ambiguous");
      return true;
    }

    main_symbol=matches.front();
  }
  else
    main_symbol=standard_main;
    
  // look it up
  contextt::symbolst::const_iterator s_it=context.symbols.find(main_symbol);
  
  if(s_it==context.symbols.end())
  {
    messaget message(message_handler);
    message.error("main symbol `"+id2string(main_symbol)+"' not in context");
    return true; // give up, no main
  }
    
  const symbolt &symbol=s_it->second;
  
  // check if it has a body
  if(symbol.value.is_nil())
  {
    messaget message(message_handler);
    message.error("main symbol `"+id2string(main_symbol)+"' has no body");
    return false; // give up
  }

  if(static_lifetime_init(context, symbol.location, message_handler))
    return true;
  
  code_blockt init_code;
  
  // build call to initialization function

  {
    contextt::symbolst::iterator init_it=
      context.symbols.find("c::__CPROVER_initialize");

    if(init_it==context.symbols.end())
      throw "failed to find __CPROVER_initialize symbol";
  
    code_function_callt call_init;
    call_init.lhs().make_nil();
    call_init.location()=symbol.location;
    call_init.function()=symbol_expr(init_it->second);

    init_code.move_to_operands(call_init);
  }

  // build call to main function
  
  code_function_callt call_main;
  call_main.location()=symbol.location;
  call_main.function()=symbol_expr(symbol);

  const code_typet::argumentst &arguments=
    to_code_type(symbol.type).arguments();

  if(symbol.name==standard_main)
  {
    if(arguments.size()==0)
    {
      // ok
    }
    else if(arguments.size()==2 || arguments.size()==3)
    {
      namespacet ns(context);

      const symbolt &argc_symbol=ns.lookup("c::argc'");
      const symbolt &argv_symbol=ns.lookup("c::argv'");
      
      {
        // assume argc is at least one
        exprt one=from_integer(1, argc_symbol.type);
        
        exprt ge(ID_ge, typet(ID_bool));
        ge.copy_to_operands(symbol_expr(argc_symbol), one);
        
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
        le.copy_to_operands(symbol_expr(argc_symbol), bound_expr);
        
        codet assumption;
        assumption.set_statement(ID_assume);
        assumption.move_to_operands(le);
        init_code.move_to_operands(assumption);
      }
      
      if(arguments.size()==3)
      {        
        const symbolt &envp_size_symbol=ns.lookup("c::envp_size'");

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
        le.copy_to_operands(symbol_expr(envp_size_symbol), max_minus_one);
        
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
        index.copy_to_operands(zero_string, gen_zero(uint_type()));
        exprt address_of("address_of", pointer_typet());
        address_of.type().subtype()=char_type();
        address_of.copy_to_operands(index);

        if(argv_symbol.type.subtype()!=address_of.type())
          address_of.make_typecast(argv_symbol.type.subtype());
        
        // assign argv[*] to the address of a string-object
        exprt array_of("array_of", argv_symbol.type);
        array_of.copy_to_operands(address_of);
        
        init_code.copy_to_operands(
          code_assignt(symbol_expr(argv_symbol), array_of));
        */
      }

      {
        // assign argv[argc] to NULL
        exprt null(ID_constant, argv_symbol.type.subtype());
        null.set(ID_value, ID_NULL);
        
        exprt index_expr(ID_index, argv_symbol.type.subtype());
        index_expr.copy_to_operands(
          symbol_expr(argv_symbol),
          symbol_expr(argc_symbol));
          
        // disable bounds check on that one
        index_expr.set("bounds_check", false);

        init_code.copy_to_operands(code_assignt(index_expr, null));
      }

      if(arguments.size()==3)
      {        
        const symbolt &envp_symbol=ns.lookup("c::envp'");
        const symbolt &envp_size_symbol=ns.lookup("c::envp_size'");
        
        // assume envp[envp_size] is NULL
        exprt null(ID_constant, envp_symbol.type.subtype());
        null.set(ID_value, ID_NULL);
        
        exprt index_expr(ID_index, envp_symbol.type.subtype());
        index_expr.copy_to_operands(
          symbol_expr(envp_symbol),
          symbol_expr(envp_size_symbol));
          
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

        if(arguments.size()==3)
          operands.resize(3);
        else 
          operands.resize(2);
          
        exprt &op0=operands[0];
        exprt &op1=operands[1];
        
        op0=symbol_expr(argc_symbol);
        
        {
          const exprt &arg1=arguments[1];

          exprt index_expr(ID_index, arg1.type().subtype());
          index_expr.copy_to_operands(symbol_expr(argv_symbol), gen_zero(index_type()));

          // disable bounds check on that one
          index_expr.set("bounds_check", false);
        
          op1=exprt(ID_address_of, arg1.type());
          op1.move_to_operands(index_expr);
        }

        // do we need envp?
        if(arguments.size()==3)
        {
          const symbolt &envp_symbol=ns.lookup("c::envp'");
          exprt &op2=operands[2];

          const exprt &arg2=arguments[2];
          
          exprt index_expr(ID_index, arg2.type().subtype());
          index_expr.copy_to_operands(
            symbol_expr(envp_symbol), gen_zero(index_type()));
            
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
    call_main.arguments()=build_function_environment(arguments);
  }

  init_code.move_to_operands(call_main);

  // add "main"
  symbolt new_symbol;

  code_typet main_type;
  main_type.return_type()=empty_typet();
  
  new_symbol.name=ID_main;
  new_symbol.type.swap(main_type);
  new_symbol.value.swap(init_code);
  
  if(context.move(new_symbol))
  {
    messaget message;
    message.set_message_handler(message_handler);
    message.error("failed to move main symbol");
    return true;
  }
  
  return false;
}
