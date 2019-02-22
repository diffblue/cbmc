/******************************************************************\

Module: recursive_initialization

Author: Diffblue Ltd.

\******************************************************************/

#include "recursive_initialization.h"

#include <util/allocate_objects.h>
#include <util/c_types.h>
#include <util/fresh_symbol.h>
#include <util/irep.h>
#include <util/std_code.h>
#include <util/std_expr.h>

recursive_initializationt::recursive_initializationt(
  recursive_initialization_configt initialization_config,
  goto_modelt &goto_model)
  : initialization_config(std::move(initialization_config)),
    goto_model(goto_model)
{
}

void recursive_initializationt::initialize(
  const exprt &lhs,
  std::size_t depth,
  const recursion_sett &known_tags,
  code_blockt &body)
{
  auto const &type = lhs.type();
  if(type.id() == ID_struct_tag)
  {
    initialize_struct_tag(lhs, depth, known_tags, body);
  }
  else if(type.id() == ID_pointer)
  {
    initialize_pointer(lhs, depth, known_tags, body);
  }
  else
  {
    initialize_nondet(lhs, depth, known_tags, body);
  }
}

symbol_exprt recursive_initializationt::get_malloc_function()
{
  // unused for now, we'll need it for arrays
  auto malloc_sym = goto_model.symbol_table.lookup("malloc");
  if(malloc_sym == nullptr)
  {
    symbolt new_malloc_sym;
    new_malloc_sym.type = code_typet{code_typet{
      {code_typet::parametert{size_type()}}, pointer_type(empty_typet{})}};
    new_malloc_sym.name = new_malloc_sym.pretty_name =
      new_malloc_sym.base_name = "malloc";
    new_malloc_sym.mode = initialization_config.mode;
    goto_model.symbol_table.insert(new_malloc_sym);
    return new_malloc_sym.symbol_expr();
  }
  return malloc_sym->symbol_expr();
}

void recursive_initializationt::initialize_struct_tag(
  const exprt &lhs,
  std::size_t depth,
  const recursion_sett &known_tags,
  code_blockt &body)
{
  PRECONDITION(lhs.type().id() == ID_struct_tag);
  auto const &type = to_struct_tag_type(lhs.type());
  auto new_known_tags = known_tags;
  new_known_tags.insert(type.get_identifier());
  auto const &ns = namespacet{goto_model.symbol_table};
  for(auto const &component : ns.follow_tag(type).components())
  {
    initialize(member_exprt{lhs, component}, depth, new_known_tags, body);
  }
}

void recursive_initializationt::initialize_pointer(
  const exprt &lhs,
  std::size_t depth,
  const recursion_sett &known_tags,
  code_blockt &body)
{
  PRECONDITION(lhs.type().id() == ID_pointer);
  auto const &type = to_pointer_type(lhs.type());
  allocate_objectst allocate_objects{initialization_config.mode,
                                     type.source_location(),
                                     "initializer",
                                     goto_model.symbol_table};
  exprt choice =
    allocate_objects.allocate_automatic_local_object(bool_typet{}, "choice");
  symbolt &pointee_symbol = get_fresh_aux_symbol(
    type.subtype(),
    "__goto_harness",
    "pointee",
    lhs.source_location(),
    initialization_config.mode,
    goto_model.symbol_table);
  pointee_symbol.is_static_lifetime = true;
  pointee_symbol.is_lvalue = true;

  auto pointee = pointee_symbol.symbol_expr();
  allocate_objects.declare_created_symbols(body);
  body.add(code_assignt{lhs, null_pointer_exprt{type}});
  bool is_unknown_struct_tag =
    can_cast_type<tag_typet>(type.subtype()) &&
    known_tags.find(to_tag_type(type.subtype()).get_identifier()) ==
      known_tags.end();

  if(
    depth < initialization_config.max_nondet_tree_depth ||
    is_unknown_struct_tag)
  {
    if(depth < initialization_config.min_null_tree_depth)
    {
      initialize(pointee, depth + 1, known_tags, body);
      body.add(code_assignt{lhs, address_of_exprt{pointee}});
    }
    else
    {
      code_blockt then_case{};
      initialize(pointee, depth + 1, known_tags, then_case);
      then_case.add(code_assignt{lhs, address_of_exprt{pointee}});
      body.add(code_ifthenelset{choice, then_case});
    }
  }
}

void recursive_initializationt::initialize_nondet(
  const exprt &lhs,
  std::size_t depth,
  const recursion_sett &known_tags,
  code_blockt &body)
{
  body.add(code_assignt{lhs, side_effect_expr_nondett{lhs.type()}});
}
