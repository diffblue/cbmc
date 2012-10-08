/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <algorithm>
#include <expr_util.h>
#include <arith_tools.h>
#include <i2string.h>
#include <location.h>
#include <symbol.h>

#include <linking/zero_initializer.h>
#include <ansi-c/c_typecast.h>

#include "cpp_typecheck.h"
#include "expr2cpp.h"
#include "cpp_convert_type.h"
#include "cpp_declarator.h"

/*******************************************************************\

Function: cpp_typecheckt::this_struct_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const struct_typet &cpp_typecheckt::this_struct_type()
{
  const exprt &this_expr=
    cpp_scopes.current_scope().this_expr;

  assert(this_expr.is_not_nil());
  assert(this_expr.type().id()==ID_pointer);

  const typet &t=follow(this_expr.type().subtype());
  assert(t.id()==ID_struct);
  return to_struct_type(t);
}

/*******************************************************************\

Function: cpp_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string cpp_typecheckt::to_string(const exprt &expr)
{
  return expr2cpp(expr, *this);
}

/*******************************************************************\

Function: cpp_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string cpp_typecheckt::to_string(const typet &type)
{
  return type2cpp(type, *this);
}

/*******************************************************************\

Function: cpp_typecheckt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::convert(cpp_itemt &item)
{
  if(item.is_declaration())
    convert(to_cpp_declaration(item));
  else if(item.is_linkage_spec())
    convert(item.get_linkage_spec());
  else if(item.is_namespace_spec())
    convert(item.get_namespace_spec());
  else if(item.is_using())
    convert(item.get_using());
  else
  {
    err_location(item);
    throw "unknown parse-tree element: "+item.id_string();
  }
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck()
{
  // default linkage is "automatic"
  current_linkage_spec=ID_auto;
  
  for(cpp_parse_treet::itemst::iterator
      it=cpp_parse_tree.items.begin();
      it!=cpp_parse_tree.items.end();
      it++)
    convert(*it);

  static_and_dynamic_initialization();

  do_not_typechecked();

  clean_up();
}

/*******************************************************************\

Function: cpp_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cpp_typecheck(
  cpp_parse_treet &cpp_parse_tree,
  contextt &context,
  const std::string &module,
  message_handlert &message_handler)
{
  cpp_typecheckt cpp_typecheck(cpp_parse_tree, context, module, message_handler);
  return cpp_typecheck.typecheck_main();
}

/*******************************************************************\

Function: cpp_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cpp_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns)
{
  contextt context;
  cpp_parse_treet cpp_parse_tree;

  cpp_typecheckt cpp_typecheck(cpp_parse_tree, context,
                               ns.get_context(), "", message_handler);

  try
  {
    cpp_typecheck.typecheck_expr(expr);
  }

  catch(int e)
  {
    cpp_typecheck.error();
  }

  catch(const char *e)
  {
    cpp_typecheck.error(e);
  }

  catch(const std::string &e)
  {
    cpp_typecheck.error(e);
  }

  return cpp_typecheck.get_error_found();
}

/*******************************************************************\

Function: cpp_typecheckt::static_and_dynamic_initialization

  Inputs:

 Outputs:

 Purpose: Initialization of static objects:

 "Objects with static storage duration (3.7.1) shall be zero-initialized
 (8.5) before any other initialization takes place. Zero-initialization
 and initialization with a constant expression are collectively called
 static initialization; all other initialization is dynamic
 initialization. Objects of POD types (3.9) with static storage duration
 initialized with constant expressions (5.19) shall be initialized before
 any dynamic initialization takes place. Objects with static storage
 duration defined in namespace scope in the same translation unit and
 dynamically initialized shall be initialized in the order in which their
 definition appears in the translation unit. [Note: 8.5.1 describes the
 order in which aggregate members are initialized. The initialization
 of local static objects is described in 6.7. ]"

\*******************************************************************/

void cpp_typecheckt::static_and_dynamic_initialization()
{
  code_blockt init_block; // Dynamic Initialization Block

  disable_access_control = true;

  // fill in any missing zero initializers
  // for static initialization
  Forall_symbols(s_it, context.symbols)
  {
    symbolt &symbol=s_it->second;

    if(!symbol.is_static_lifetime)
      continue;
      
    if(symbol.mode!=ID_cpp)
      continue;
      
    // magic value
    if(symbol.name=="c::__CPROVER::constant_infinity_uint")
      continue;

    // it has a non-code initializer already?
    if(symbol.value.is_not_nil() &&
       symbol.value.id()!=ID_code)
      continue;
      
    // it's a declaration only
    if(symbol.is_extern)
      continue;

    if(!symbol.is_lvalue)
      continue;

    if(cpp_is_pod(symbol.type))
      symbol.value=::zero_initializer(symbol.type, symbol.location, *this, get_message_handler());
    else
    {
      // _always_ zero initialize,
      // even if there is already an initializer.
      zero_initializer(
        cpp_symbol_expr(symbol),
        symbol.type,
        symbol.location,
        init_block.operands());
    }
  }

  for(dynamic_initializationst::const_iterator
      d_it=dynamic_initializations.begin();
      d_it!=dynamic_initializations.end();
      d_it++)
  {
    symbolt &symbol=context.symbols.find(*d_it)->second;

    if(symbol.is_extern)
      continue;
    
    // PODs are always statically initialized  
    if(cpp_is_pod(symbol.type))
      continue;

    assert(symbol.is_static_lifetime);
    assert(!symbol.is_type);
    assert(symbol.type.id()!=ID_code);

    exprt symbol_expr=cpp_symbol_expr(symbol);

    // initializer given?
    if(symbol.value.is_not_nil())
    {
      code_assignt code(symbol_expr, symbol.value);
      code.location()=symbol.location;

      init_block.move_to_operands(code);

      // Make it nil because we do not want
      // global_init to try to initialize the
      // object
      symbol.value.make_nil();
    }
    else
    {
      // use default constructor
      exprt::operandst ops;

      codet call=
        cpp_constructor(symbol.location, symbol_expr, ops);

      if(call.is_not_nil())
        init_block.move_to_operands(call);
    }
  }
  
  dynamic_initializations.clear();

  //block_sini.move_to_operands(block_dini);

  // Create the dynamic initialization procedure
  symbolt init_symbol;

  init_symbol.name="c::#cpp_dynamic_initialization#"+id2string(module);
  init_symbol.base_name="#cpp_dynamic_initialization#"+id2string(module);
  init_symbol.value.swap(init_block);
  init_symbol.mode=ID_cpp;
  init_symbol.module=module;
  init_symbol.type=code_typet();
  init_symbol.type.add(ID_return_type)=typet(ID_empty);
  init_symbol.type.set("initialization", true);
  init_symbol.is_type=false;
  init_symbol.is_macro=false;

  context.move(init_symbol);

  disable_access_control=false;
}

/*******************************************************************\

Function: cpp_typecheckt::do_not_typechecked

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::do_not_typechecked()
{
  bool cont;

  do
  {
    cont = false;

    Forall_symbols(s_it, context.symbols)
    {
      symbolt &symbol=s_it->second;

      if(symbol.value.id()=="cpp_not_typechecked" &&
         symbol.value.get_bool("is_used"))
      {
        assert(symbol.type.id()==ID_code);

        if(symbol.base_name =="operator=")
        {
          cpp_declaratort declarator;
          declarator.location() = symbol.location;
          default_assignop_value(
            lookup(symbol.type.get(ID_C_member_name)), declarator);
          symbol.value.swap(declarator.value());
          convert_function(symbol);
          cont=true;
        }
        else if(symbol.value.operands().size() == 1)
        {
          exprt tmp = symbol.value.operands()[0];
          symbol.value.swap(tmp);
          convert_function(symbol);
          cont=true;
        }
        else
          assert(0); // Don't know what to do!
      }
    }
  }
  while(cont);

  Forall_symbols(s_it, context.symbols)
  {
    symbolt &symbol=s_it->second;
    if(symbol.value.id()=="cpp_not_typechecked")
      symbol.value.make_nil();
  }
}

/*******************************************************************\

Function: cpp_typecheckt::clean_up

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::clean_up()
{
  contextt::symbolst::iterator it=context.symbols.begin();
  
  while(it!=context.symbols.end())
  {
    contextt::symbolst::iterator cur_it = it;
    it++;

    symbolt &symbol = cur_it->second;

    if(symbol.type.get_bool(ID_is_template))
    {
      context.symbols.erase(cur_it);
      continue;
    }
    else if(symbol.type.id()==ID_struct ||
            symbol.type.id()==ID_union)
    {
      struct_union_typet &struct_union_type=
        to_struct_union_type(symbol.type);

      const struct_union_typet::componentst &components=
        struct_union_type.components();

      struct_union_typet::componentst data_members;
      data_members.reserve(components.size());

      struct_union_typet::componentst &function_members=
        (struct_union_typet::componentst &)
        (struct_union_type.add(ID_methods).get_sub());
        
      function_members.reserve(components.size());

      for(struct_typet::componentst::const_iterator
          compo_it=components.begin();
          compo_it!=components.end();
          compo_it++)
      {
        if(compo_it->get_bool(ID_is_static) ||
           compo_it->get_bool(ID_is_type))
        {
          // skip it
        }
        else if(compo_it->type().id()==ID_code)
        {
          function_members.push_back(*compo_it);
        }
        else
        {
          data_members.push_back(*compo_it);
        }
      }

      struct_union_type.components().swap(data_members);
    }
  }
}
