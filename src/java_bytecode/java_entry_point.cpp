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
#include <util/i2string.h>

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
}

/*******************************************************************\

Function: gen_argument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

namespace {
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

Function: gen_nondet_init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

namespace {
void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  const namespacet &ns,
  std::set<irep_idt> &recursion_set,
  bool is_sub,
  irep_idt class_identifier)
{
  const typet &type=ns.follow(expr.type());

  if(type.id()==ID_struct)
  {
    typedef struct_typet::componentt componentt;
    typedef struct_typet::componentst componentst;

    const struct_typet &struct_type=to_struct_type(type);
    const irep_idt struct_tag=struct_type.get_tag();

    componentst components=struct_type.components();

    if(!is_sub)
      class_identifier=struct_tag;

    recursion_set.insert(struct_tag);
    assert(!recursion_set.empty());

    for(componentst::const_iterator it=components.begin();
        it!=components.end(); it++)
    {
      const componentt &component=*it;
      const typet &component_type=component.type();
      irep_idt name=component.get_name();

      member_exprt me(expr, name, component_type);

      if(name=="@class_identifier")
      {
        constant_exprt ci(class_identifier, string_typet());

        code_assignt code(me, ci);
        init_code.copy_to_operands(code);
      }
      else
      {
        irep_idt new_class_identifier;
        assert(!name.empty());

        is_sub = name[0]=='@';

        gen_nondet_init(
          me, init_code, ns, recursion_set, is_sub, class_identifier);
      }
    }

    recursion_set.erase(struct_tag);
  }
  else if(type.id()!=ID_pointer)
  {
    assert(type.id()!= ID_struct);

    side_effect_expr_nondett se=side_effect_expr_nondett(type);

    code_assignt code(expr, se);
    init_code.copy_to_operands(code);
  }
  else
  {
    assert(type.id()==ID_pointer);

    // dereferenced type
    const pointer_typet &pointer_type=to_pointer_type(type);
    const typet &subtype=ns.follow(pointer_type.subtype());

    if(subtype.id()==ID_struct)
    {
      const struct_typet &struct_type=to_struct_type(subtype);
      const irep_idt struct_tag=struct_type.get_tag();

      if(recursion_set.find(struct_tag)!=recursion_set.end())
      {
        // make null
        null_pointer_exprt null_pointer_expr(pointer_type);
        code_assignt code(expr, null_pointer_expr);
        init_code.copy_to_operands(code);

        return;
      }
    }

    // build size expression
    exprt object_size=size_of_expr(subtype, ns);

    if(subtype.id()!=ID_empty && !object_size.is_nil())
    {
      // malloc expression
      side_effect_exprt malloc_expr(ID_malloc);
      malloc_expr.copy_to_operands(object_size);
      malloc_expr.type()=pointer_type;

      code_assignt code(expr, malloc_expr);
      init_code.copy_to_operands(code);

      // dereference expression
      dereference_exprt deref_expr(expr, subtype);

      gen_nondet_init(deref_expr, init_code, ns, recursion_set, false, "");
    }
    else
    {
      // make null
      null_pointer_exprt null_pointer_expr(pointer_type);
      code_assignt code(expr, null_pointer_expr);
      init_code.copy_to_operands(code);
    }
  }
}
}

/*******************************************************************\

Function: gen_nondet_init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

namespace {
void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  const namespacet &ns)
{
  std::set<irep_idt> recursion_set;
  gen_nondet_init(expr, init_code, ns, recursion_set, false, "");
}
}

/*******************************************************************\

Function: gen_nondet_init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

namespace {
symbolt &new_tmp_symbol(symbol_tablet &symbol_table)
{
  static int temporary_counter=0;

  auxiliary_symbolt new_symbol;
  symbolt *symbol_ptr;

  do
  {
    new_symbol.name="tmp_struct_init$"+i2string(++temporary_counter);
    new_symbol.base_name=new_symbol.name;
    new_symbol.mode=ID_java;
  } while(symbol_table.move(new_symbol, symbol_ptr));

  return *symbol_ptr;
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

#if 0
  std::cout << "Main: " << config.main << std::endl;
#endif

  messaget message(message_handler);

  code_blockt struct_init_code; // struct init code if needed
  bool have_struct=false;
  symbol_exprt struct_ptr;

  symbolt symbol; // main function symbol

  // find main symbol
  if(config.main!="")
  {
    // look it up
    symbol_tablet::symbolst::const_iterator s_it
      =symbol_table.symbols.find(config.main);

    if(s_it==symbol_table.symbols.end())
    {
      message.error() << "main symbol `" << config.main
                      << "' not found" << messaget::eom;
      return true;
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

    // get name of associated struct
    size_t idx=config.main.rfind(".");
    assert(idx!=std::string::npos);
    assert(idx<config.main.size());
    std::string st=config.main.substr(0, idx);
#if 0
    std::cout << "Struct name: " << st << std::endl;
#endif

    // look it up
    symbol_tablet::symbolst::const_iterator st_it
      =symbol_table.symbols.find(st);

    if(st_it!=symbol_table.symbols.end() &&
       st_it->second.type.id()==ID_struct)
    {
      const symbolt &struct_symbol=st_it->second;
      assert(struct_symbol.type.id()==ID_struct);
      const struct_typet &struct_type=to_struct_type(struct_symbol.type);
      const pointer_typet pointer_type(struct_type);

      symbolt &aux_symbol=new_tmp_symbol(symbol_table);
      aux_symbol.type=pointer_type;
      aux_symbol.is_static_lifetime=true;

      struct_ptr=aux_symbol.symbol_expr();

      namespacet ns(symbol_table);
      gen_nondet_init(struct_ptr, struct_init_code, ns);

      have_struct=true;
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

  // add struct init code

  if(have_struct)
  {
    typedef code_blockt::operandst operandst;
    const operandst &operands=struct_init_code.operands();

    for(operandst::const_iterator it=operands.begin(); it!=operands.end(); it++)
    {
      init_code.add((const codet&)*it);
    }
  }

  // build call to main method

  code_function_callt call_main;
  call_main.add_source_location()=symbol.location;
  call_main.function()=symbol.symbol_expr();

  const code_typet::parameterst &parameters=
    to_code_type(symbol.type).parameters();

  exprt::operandst main_arguments;
  main_arguments.resize(parameters.size());

  unsigned i=0;

  if(have_struct && parameters.size()>=1)
  {
    main_arguments[0]=struct_ptr;
    i++;
  }

  for(; i<parameters.size(); i++)
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
    message.error() << "failed to move main symbol" << messaget::eom;
    return true;
  }

  return false;
}
