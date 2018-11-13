/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#include <algorithm>

#include <util/arith_tools.h>
#include <util/expr_initializer.h>
#include <util/source_location.h>
#include <util/symbol.h>

#include <ansi-c/builtin_factory.h>
#include <ansi-c/c_typecast.h>

#include "expr2cpp.h"
#include "cpp_convert_type.h"
#include "cpp_declarator.h"

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
  else if(item.is_static_assert())
    convert(item.get_static_assert());
  else
  {
    error().source_location=item.source_location();
    error() << "unknown parse-tree element: " << item.id() << eom;
    throw 0;
  }
}

/// typechecking main method
void cpp_typecheckt::typecheck()
{
  // default linkage is "automatic"
  current_linkage_spec=ID_auto;

  for(auto &item : cpp_parse_tree.items)
    convert(item);

  typecheck_method_bodies();

  static_and_dynamic_initialization();

  do_not_typechecked();

  clean_up();
}

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

std::string cpp_typecheckt::to_string(const exprt &expr)
{
  return expr2cpp(expr, *this);
}

std::string cpp_typecheckt::to_string(const typet &type)
{
  return type2cpp(type, *this);
}

bool cpp_typecheck(
  cpp_parse_treet &cpp_parse_tree,
  symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  cpp_typecheckt cpp_typecheck(
    cpp_parse_tree, symbol_table, module, message_handler);
  return cpp_typecheck.typecheck_main();
}

bool cpp_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns)
{
  const unsigned errors_before=
    message_handler.get_message_count(messaget::M_ERROR);

  symbol_tablet symbol_table;
  cpp_parse_treet cpp_parse_tree;

  cpp_typecheckt cpp_typecheck(cpp_parse_tree, symbol_table,
                               ns.get_symbol_table(), "", message_handler);

  try
  {
    cpp_typecheck.typecheck_expr(expr);
  }

  catch(int)
  {
    cpp_typecheck.error();
  }

  catch(const char *e)
  {
    cpp_typecheck.error() << e << messaget::eom;
  }

  catch(const std::string &e)
  {
    cpp_typecheck.error() << e << messaget::eom;
  }

  return message_handler.get_message_count(messaget::M_ERROR)!=errors_before;
}

/// Initialization of static objects:
///
/// "Objects with static storage duration (3.7.1) shall be zero-initialized
/// (8.5) before any other initialization takes place. Zero-initialization
/// and initialization with a constant expression are collectively called
/// static initialization; all other initialization is dynamic
/// initialization. Objects of POD types (3.9) with static storage duration
/// initialized with constant expressions (5.19) shall be initialized before
/// any dynamic initialization takes place. Objects with static storage
/// duration defined in namespace scope in the same translation unit and
/// dynamically initialized shall be initialized in the order in which their
/// definition appears in the translation unit. [Note: 8.5.1 describes the
/// order in which aggregate members are initialized. The initialization
/// of local static objects is described in 6.7. ]"
void cpp_typecheckt::static_and_dynamic_initialization()
{
  code_blockt init_block; // Dynamic Initialization Block

  disable_access_control = true;

  for(const irep_idt &d_it : dynamic_initializations)
  {
    const symbolt &symbol=*symbol_table.lookup(d_it);

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
      // This will be a constructor call,
      // which we execute.
      init_block.add(to_code(symbol.value));

      // Make it nil to get zero initialization by
      // __CPROVER_initialize
      symbol_table.get_writeable_ref(d_it).value.make_nil();
    }
    else
    {
      // use default constructor
      exprt::operandst ops;

      auto call = cpp_constructor(symbol.location, symbol_expr, ops);

      if(call.has_value())
        init_block.add(call.value());
    }
  }

  dynamic_initializations.clear();

  // block_sini.move_to_operands(block_dini);

  // Create the dynamic initialization procedure
  symbolt init_symbol;

  init_symbol.name="#cpp_dynamic_initialization#"+id2string(module);
  init_symbol.base_name="#cpp_dynamic_initialization#"+id2string(module);
  init_symbol.value.swap(init_block);
  init_symbol.mode=ID_cpp;
  init_symbol.module=module;
  init_symbol.type = code_typet({}, typet(ID_constructor));
  init_symbol.is_type=false;
  init_symbol.is_macro=false;

  symbol_table.insert(std::move(init_symbol));

  disable_access_control=false;
}

void cpp_typecheckt::do_not_typechecked()
{
  bool cont;

  do
  {
    cont = false;

    for(const auto &named_symbol : symbol_table.symbols)
    {
      const symbolt &symbol=named_symbol.second;

      if(
        symbol.value.id() == ID_cpp_not_typechecked &&
        symbol.value.get_bool(ID_is_used))
      {
        assert(symbol.type.id()==ID_code);
        exprt value = symbol.value;

        if(symbol.base_name=="operator=")
        {
          cpp_declaratort declarator;
          declarator.add_source_location() = symbol.location;
          default_assignop_value(
            lookup(symbol.type.get(ID_C_member_name)), declarator);
          value.swap(declarator.value());
          cont=true;
        }
        else if(symbol.value.operands().size()==1)
        {
          value = symbol.value.op0();
          cont=true;
        }
        else
          UNREACHABLE; // Don't know what to do!

        symbolt &writable_symbol =
          *symbol_table.get_writeable(named_symbol.first);
        writable_symbol.value.swap(value);
        convert_function(writable_symbol);
      }
    }
  }
  while(cont);

  for(const auto &named_symbol : symbol_table.symbols)
  {
    if(named_symbol.second.value.id() == ID_cpp_not_typechecked)
      symbol_table.get_writeable_ref(named_symbol.first).value.make_nil();
  }
}

void cpp_typecheckt::clean_up()
{
  symbol_tablet::symbolst::const_iterator it=symbol_table.symbols.begin();

  while(it!=symbol_table.symbols.end())
  {
    symbol_tablet::symbolst::const_iterator cur_it = it;
    it++;

    const symbolt &symbol=cur_it->second;

    // erase templates
    if(symbol.type.get_bool(ID_is_template) ||
       // Remove all symbols that have not been converted.
       //   In particular this includes symbols created for functions
       //   during template instantiation that are never called,
       //   and hence, their bodies have not been converted.
       contains_cpp_name(symbol.value))
    {
      symbol_table.erase(cur_it);
      continue;
    }
    else if(symbol.type.id()==ID_struct ||
            symbol.type.id()==ID_union)
    {
      // remove methods from 'components'
      struct_union_typet &struct_union_type=to_struct_union_type(
        symbol_table.get_writeable_ref(cur_it->first).type);

      const struct_union_typet::componentst &components=
        struct_union_type.components();

      struct_union_typet::componentst data_members;
      data_members.reserve(components.size());

      struct_union_typet::componentst &function_members=
        (struct_union_typet::componentst &)
        (struct_union_type.add(ID_methods).get_sub());

      function_members.reserve(components.size());

      for(const auto &compo_it : components)
      {
        if(compo_it.get_bool(ID_is_static) ||
           compo_it.get_bool(ID_is_type))
        {
          // skip it
        }
        else if(compo_it.type().id()==ID_code)
        {
          function_members.push_back(compo_it);
        }
        else
        {
          data_members.push_back(compo_it);
        }
      }

      struct_union_type.components().swap(data_members);
    }
  }
}

bool cpp_typecheckt::builtin_factory(const irep_idt &identifier)
{
  return ::builtin_factory(identifier, symbol_table, get_message_handler());
}

bool cpp_typecheckt::contains_cpp_name(const exprt &expr)
{
  if(expr.id() == ID_cpp_name || expr.id() == ID_cpp_declaration)
    return true;
  forall_operands(it, expr)
    if(contains_cpp_name(*it))
      return true;
  return false;
}
