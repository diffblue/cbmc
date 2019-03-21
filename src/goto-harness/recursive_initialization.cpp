/******************************************************************\

Module: recursive_initialization

Author: Diffblue Ltd.

\******************************************************************/

#include "recursive_initialization.h"

#include <util/allocate_objects.h>
#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/fresh_symbol.h>
#include <util/irep.h>
#include <util/optional_utils.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <functional>

recursive_initializationt::recursive_initializationt(
  recursive_initialization_configt initialization_config,
  goto_modelt &goto_model)
  : initialization_config(std::move(initialization_config)),
    goto_model(goto_model)
{
}

void recursive_initializationt::initialize(
  const exprt &lhs,
  const std::size_t depth,
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
    if(lhs.id() == ID_symbol)
    {
      auto const &lhs_symbol = to_symbol_expr(lhs);
      if(should_be_treated_as_cstring(lhs_symbol.get_identifier()))
      {
        initialize_cstring(lhs, depth, known_tags, body);
        return;
      }
      else if(should_be_treated_as_array(lhs_symbol.get_identifier()))
      {
        initialize_dynamic_array(
          lhs, depth, known_tags, body, default_array_member_initialization());
        return;
      }
    }
    initialize_pointer(lhs, depth, known_tags, body);
  }
  else if(type.id() == ID_array)
  {
    initialize_array(
      lhs, depth, known_tags, body, default_array_member_initialization());
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
  const std::size_t depth,
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
  const std::size_t depth,
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
  body.add(code_assignt{lhs, null_pointer_exprt{type}, type.source_location()});
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
  const std::size_t depth,
  const recursion_sett &known_tags,
  code_blockt &body)
{
  if(
    lhs.id() != ID_symbol ||
    !is_array_size_parameter(to_symbol_expr(lhs).get_identifier()))
  {
    body.add(code_assignt{lhs, side_effect_expr_nondett{lhs.type()}});
  }
}

void recursive_initializationt::initialize_array(
  const exprt &array,
  const std::size_t depth,
  const recursion_sett &known_tags,
  code_blockt &body,
  array_convertert array_member_initialization)
{
  PRECONDITION(array.type().id() == ID_array);
  const auto &array_type = to_array_type(array.type());
  const auto array_size =
    numeric_cast_v<std::size_t>(to_constant_expr(array_type.size()));
  for(std::size_t index = 0; index < array_size; index++)
  {
    array_member_initialization(
      array, array_size, index, depth, known_tags, body);
  }
}

bool recursive_initializationt::should_be_treated_as_array(
  const irep_idt &array_name) const
{
  return initialization_config.pointers_to_treat_as_arrays.find(array_name) !=
         initialization_config.pointers_to_treat_as_arrays.end();
}

bool recursive_initializationt::is_array_size_parameter(
  const irep_idt &cmdline_arg) const
{
  return initialization_config.variables_that_hold_array_sizes.find(
           cmdline_arg) !=
         initialization_config.variables_that_hold_array_sizes.end();
}

optionalt<irep_idt> recursive_initializationt::get_associated_size_variable(
  const irep_idt &array_name) const
{
  return optional_lookup(
    initialization_config.array_name_to_associated_array_size_variable,
    array_name);
}

bool recursive_initializationt::should_be_treated_as_cstring(
  const irep_idt &pointer_name) const
{
  return initialization_config.pointers_to_treat_as_cstrings.count(
           pointer_name) != 0;
}

void recursive_initializationt::initialize_dynamic_array(
  const exprt &pointer,
  const std::size_t depth,
  const recursion_sett &known_tags,
  code_blockt &body,
  array_convertert array_initialization)
{
  PRECONDITION(pointer.type().id() == ID_pointer);

  // size_t number_of_arrays = max_array_size - min_array_size;
  // T *arrays[number_of_arrays];
  //
  // T array1[min_array_size];
  // initialize(array1);
  // arrays[0] = &array1[0];
  //
  // T array2[min_array_size+1];
  // initialize(array2);
  // arrays[1] = &array2[0];
  //
  // ... and so on ...
  //
  // T arrayN[max_array_size];
  // initialize(arrayN);
  // arrays[number_of_arrays-1] = &arrayN[0];
  //
  // size_t array_index;
  // assume(0 <= array_index < number_of_arrays);
  // actual_size = array_index + min_array_size;
  // array_pointer = arrays[array_index];

  const auto &pointer_type = to_pointer_type(pointer.type());
  allocate_objectst allocate_objects{initialization_config.mode,
                                     pointer_type.source_location(),
                                     "initializer",
                                     goto_model.symbol_table};
  const auto min_array_size = initialization_config.min_dynamic_array_size;
  const auto max_array_size = initialization_config.max_dynamic_array_size;
  PRECONDITION(max_array_size >= min_array_size);
  const auto number_of_arrays = max_array_size - min_array_size + 1;

  auto const array_variables = [&]() {
    std::vector<symbol_exprt> array_variables;
    for(auto array_size = min_array_size; array_size <= max_array_size;
        array_size++)
    {
      array_variables.push_back(
        allocate_objects.allocate_automatic_local_object(
          array_typet{pointer_type.subtype(),
                      from_integer(array_size, size_type())},
          "array"));
    }
    return array_variables;
  }();

  const auto arrays = allocate_objects.allocate_automatic_local_object(
    array_typet{pointer_type, from_integer(number_of_arrays, size_type())},
    "arrays");

  const auto nondet_index = allocate_objects.allocate_automatic_local_object(
    size_type(), "nondet_index");

  allocate_objects.declare_created_symbols(body);

  {
    std::size_t array_counter = 0;
    for(const auto &array_variable : array_variables)
    {
      initialize_array(
        array_variable, depth + 1, known_tags, body, array_initialization);
      body.add(code_assignt{
        index_exprt{arrays, from_integer(array_counter++, size_type())},
        address_of_exprt{
          index_exprt{array_variable, from_integer(0, size_type())}}});
    }
    INVARIANT(array_counter == number_of_arrays, "initialized all arrays");
  }

  body.add(code_assumet{and_exprt{
    binary_relation_exprt{nondet_index, ID_ge, from_integer(0, size_type())},
    binary_relation_exprt{
      nondet_index, ID_lt, from_integer(number_of_arrays, size_type())}}});

  if(pointer.id() == ID_symbol)
  {
    const auto array_id = to_symbol_expr(pointer).get_identifier();
    const auto size_var = get_associated_size_variable(array_id);
    if(size_var.has_value())
    {
      const auto size_var_symbol_expr =
        goto_model.symbol_table.lookup_ref(size_var.value()).symbol_expr();
      body.add(code_assignt{
        size_var_symbol_expr,
        typecast_exprt{
          plus_exprt{nondet_index,
                     from_integer(min_array_size, nondet_index.type())},
          size_var_symbol_expr.type()}});
    }
  }

  body.add(code_assignt{pointer, index_exprt{arrays, nondet_index}});
}

void recursive_initializationt::initialize_cstring(
  const exprt &pointer,
  std::size_t depth,
  const recursion_sett &known_tags,
  code_blockt &body)
{
  initialize_dynamic_array(
    pointer, depth, known_tags, body, cstring_member_initialization());
}

std::string recursive_initialization_configt::to_string() const
{
  std::ostringstream out{};
  out << "recursive_initialization_config {"
      << "\n  min_null_tree_depth = " << min_null_tree_depth
      << "\n  max_nondet_tree_depth = " << max_nondet_tree_depth
      << "\n  mode = " << mode
      << "\n  max_dynamic_array_size = " << max_dynamic_array_size
      << "\n  min_dynamic_array_size = " << min_dynamic_array_size
      << "\n  pointers_to_treat_as_arrays = [";
  for(auto const &pointer : pointers_to_treat_as_arrays)
  {
    out << "\n    " << pointer;
  }
  out << "\n  ]"
      << "\n  variables_that_hold_array_sizes = [";
  for(auto const &array_size : variables_that_hold_array_sizes)
  {
    out << "\n    " << array_size;
  }
  out << "\n  ]";
  out << "\n  array_name_to_associated_size_variable = [";
  for(auto const &associated_array_size :
      array_name_to_associated_array_size_variable)
  {
    out << "\n    " << associated_array_size.first << " -> "
        << associated_array_size.second;
  }
  out << "\n  ]";
  out << "\n  pointers_to_treat_as_cstrings = [";
  for(const auto &pointer_to_treat_as_string_name :
      pointers_to_treat_as_cstrings)
  {
    out << "\n    " << pointer_to_treat_as_string_name << std::endl;
  }
  out << "\n  ]";
  out << "\n}";
  return out.str();
}

recursive_initializationt::array_convertert
recursive_initializationt::default_array_member_initialization()
{
  return [this](
           const exprt &array,
           const std::size_t length,
           const std::size_t current_index,
           const std::size_t depth,
           const recursion_sett &known_tags,
           code_blockt &body) {
    PRECONDITION(array.type().id() == ID_array);
    initialize(
      index_exprt{array, from_integer(current_index, size_type())},
      depth,
      known_tags,
      body);
  };
}

recursive_initializationt::array_convertert
recursive_initializationt::cstring_member_initialization()
{
  return [this](
           const exprt &array,
           const std::size_t length,
           const std::size_t current_index,
           const std::size_t depth,
           const recursion_sett &known_tags,
           code_blockt &body) {
    PRECONDITION(array.type().id() == ID_array);
    PRECONDITION(array.type().subtype() == char_type());
    auto const member =
      index_exprt{array, from_integer(current_index, size_type())};
    if(current_index + 1 == length)
    {
      body.add(code_assignt{member, from_integer(0, array.type().subtype())});
    }
    else
    {
      initialize(member, depth, known_tags, body);
      // We shouldn't have `\0` anywhere but at the end of a string.
      body.add(code_assumet{
        notequal_exprt{member, from_integer(0, array.type().subtype())}});
    }
  };
}
