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
#include <util/pointer_offset_size.h>
#include <util/rename.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/string2int.h>

#include <functional>

bool recursive_initialization_configt::handle_option(
  const std::string &option,
  const std::list<std::string> &values)
{
  if(option == COMMON_HARNESS_GENERATOR_MIN_NULL_TREE_DEPTH_OPT)
  {
    auto const value =
      harness_options_parser::require_exactly_one_value(option, values);
    auto const user_min_null_tree_depth =
      string2optional<std::size_t>(value, 10);
    if(user_min_null_tree_depth.has_value())
    {
      min_null_tree_depth = user_min_null_tree_depth.value();
    }
    else
    {
      throw invalid_command_line_argument_exceptiont{
        "failed to convert '" + value + "' to integer",
        "--" COMMON_HARNESS_GENERATOR_MIN_NULL_TREE_DEPTH_OPT};
    }
    return true;
  }
  else if(option == COMMON_HARNESS_GENERATOR_MAX_NONDET_TREE_DEPTH_OPT)
  {
    auto const value =
      harness_options_parser::require_exactly_one_value(option, values);
    auto const user_max_nondet_tree_depth =
      string2optional<std::size_t>(value, 10);
    if(user_max_nondet_tree_depth.has_value())
    {
      max_nondet_tree_depth = user_max_nondet_tree_depth.value();
    }
    else
    {
      throw invalid_command_line_argument_exceptiont{
        "failed to convert '" + value + "' to integer",
        "--" COMMON_HARNESS_GENERATOR_MAX_NONDET_TREE_DEPTH_OPT};
    }
    return true;
  }
  else if(option == COMMON_HARNESS_GENERATOR_MAX_ARRAY_SIZE_OPT)
  {
    max_dynamic_array_size = harness_options_parser::require_one_size_value(
      COMMON_HARNESS_GENERATOR_MAX_ARRAY_SIZE_OPT, values);
    return true;
  }
  else if(option == COMMON_HARNESS_GENERATOR_MIN_ARRAY_SIZE_OPT)
  {
    min_dynamic_array_size = harness_options_parser::require_one_size_value(
      COMMON_HARNESS_GENERATOR_MIN_ARRAY_SIZE_OPT, values);
    return true;
  }
  return false;
}

recursive_initializationt::recursive_initializationt(
  recursive_initialization_configt initialization_config,
  goto_modelt &goto_model)
  : initialization_config(std::move(initialization_config)),
    goto_model(goto_model),
    max_depth_var_name(get_fresh_global_name(
      "max_depth",
      from_integer(
        initialization_config.max_nondet_tree_depth,
        signed_int_type()))),
    min_depth_var_name(get_fresh_global_name(
      "min_depth",
      from_integer(
        initialization_config.min_null_tree_depth,
        signed_int_type())))
{
}

void recursive_initializationt::initialize(
  const exprt &lhs,
  const exprt &depth,
  code_blockt &body)
{
  const irep_idt &fun_name = build_constructor(lhs);
  const symbolt &fun_symbol = goto_model.symbol_table.lookup_ref(fun_name);

  if(lhs.id() == ID_symbol)
  {
    const irep_idt &lhs_name = to_symbol_expr(lhs).get_identifier();
    if(should_be_treated_as_array(lhs_name))
    {
      auto size_var = get_associated_size_variable(lhs_name);
      if(size_var.has_value())
      {
        const symbol_exprt &size_symbol =
          goto_model.symbol_table.lookup_ref(size_var.value()).symbol_expr();
        body.add(code_function_callt{
          fun_symbol.symbol_expr(),
          {depth, address_of_exprt{lhs}, address_of_exprt{size_symbol}}});
      }
      else
      {
        const auto &fun_type_params =
          to_code_type(fun_symbol.type).parameters();
        const typet &size_var_type = fun_type_params.back().type();
        body.add(code_function_callt{
          fun_symbol.symbol_expr(),
          {depth,
           address_of_exprt{lhs},
           null_pointer_exprt{pointer_type(size_var_type)}}});
      }
      return;
    }
    for(const auto &irep_pair :
        initialization_config.array_name_to_associated_array_size_variable)
    {
      // skip initialisation of array-size variables
      if(irep_pair.second == lhs_name)
        return;
    }
  }
  body.add(code_function_callt{fun_symbol.symbol_expr(),
                               {depth, address_of_exprt{lhs}}});
}

code_blockt recursive_initializationt::build_constructor_body(
  const exprt &depth_symbol,
  const exprt &result_symbol,
  const optionalt<exprt> &size_symbol,
  const optionalt<irep_idt> &lhs_name)
{
  PRECONDITION(result_symbol.type().id() == ID_pointer);
  const typet &type = result_symbol.type().subtype();
  if(type.id() == ID_struct_tag)
  {
    return build_struct_constructor(depth_symbol, result_symbol);
  }
  else if(type.id() == ID_pointer)
  {
    if(lhs_name.has_value())
    {
      if(should_be_treated_as_cstring(*lhs_name) && type == char_type())
        return build_array_string_constructor(result_symbol);
      else if(should_be_treated_as_array(*lhs_name))
      {
        CHECK_RETURN(size_symbol.has_value());
        return build_dynamic_array_constructor(
          depth_symbol, result_symbol, *size_symbol, lhs_name);
      }
    }
    return build_pointer_constructor(depth_symbol, result_symbol);
  }
  else if(type.id() == ID_array)
  {
    return build_array_constructor(depth_symbol, result_symbol);
  }
  else
  {
    return build_nondet_constructor(result_symbol);
  }
}

const irep_idt &recursive_initializationt::build_constructor(const exprt &expr)
{
  // for `expr` of type T builds a declaration of a function:
  //
  // void type_constructor_T(int depth_T, T *result);
  //
  // or in case a `size` is associated with the `expr`
  //
  // void type_constructor_T(int depth_T, T *result_T, int *size);
  optionalt<irep_idt> size_var;
  optionalt<irep_idt> expr_name;
  if(expr.id() == ID_symbol)
  {
    expr_name = to_symbol_expr(expr).get_identifier();
    if(should_be_treated_as_array(*expr_name))
      size_var = get_associated_size_variable(*expr_name);
  }
  const typet &type = expr.type();
  if(type_constructor_names.find(type) != type_constructor_names.end())
    return type_constructor_names[type];

  const std::string &pretty_type = type2id(type);
  symbolt &depth_symbol =
    get_fresh_param_symbol("depth_" + pretty_type, signed_int_type());
  depth_symbol.value = from_integer(0, signed_int_type());

  code_typet::parameterst fun_params;
  code_typet::parametert depth_parameter{signed_int_type()};
  depth_parameter.set_identifier(depth_symbol.name);
  fun_params.push_back(depth_parameter);

  const typet &result_type = pointer_type(type);
  const symbolt &result_symbol =
    get_fresh_param_symbol("result_" + pretty_type, result_type);
  code_typet::parametert result_parameter{result_type};
  result_parameter.set_identifier(result_symbol.name);
  fun_params.push_back(result_parameter);

  auto &symbol_table = goto_model.symbol_table;
  optionalt<exprt> size_symbol_expr;
  if(expr_name.has_value() && should_be_treated_as_array(*expr_name))
  {
    typet size_var_type;
    if(size_var.has_value())
    {
      const symbol_exprt &size_var_symbol_expr =
        symbol_table.lookup_ref(*size_var).symbol_expr();
      size_var_type = pointer_type(size_var_symbol_expr.type());
    }
    else
      size_var_type = pointer_type(signed_int_type());

    const symbolt &size_symbol =
      get_fresh_param_symbol("size_" + pretty_type, size_var_type);
    fun_params.push_back(code_typet::parametert{size_var_type});
    fun_params.back().set_identifier(size_symbol.name);
    size_symbol_expr = size_symbol.symbol_expr();
  }
  const symbolt &function_symbol = get_fresh_fun_symbol(
    "type_constructor_" + pretty_type, code_typet{fun_params, empty_typet{}});
  type_constructor_names[type] = function_symbol.name;
  symbolt *mutable_symbol = symbol_table.get_writeable(function_symbol.name);

  // the body is specific for each type of expression
  mutable_symbol->value = build_constructor_body(
    depth_symbol.symbol_expr(),
    result_symbol.symbol_expr(),
    size_symbol_expr,
    // the expression name may be needed to decide if expr should be treated as
    // a string
    expr_name);

  goto_model.goto_functions.function_map[function_symbol.name].type =
    to_code_type(function_symbol.type);
  return type_constructor_names[type];
}

symbol_exprt recursive_initializationt::get_malloc_function()
{
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

irep_idt recursive_initializationt::get_fresh_global_name(
  const std::string &symbol_name,
  const exprt &initial_value) const
{
  symbolt &fresh_symbol = get_fresh_aux_symbol(
    signed_int_type(),
    CPROVER_PREFIX,
    symbol_name,
    source_locationt{},
    initialization_config.mode,
    goto_model.symbol_table);
  fresh_symbol.is_static_lifetime = true;
  fresh_symbol.is_lvalue = true;
  fresh_symbol.value = initial_value;
  return fresh_symbol.name;
}

symbol_exprt recursive_initializationt::get_fresh_global_symexpr(
  const std::string &symbol_name) const
{
  symbolt &fresh_symbol = get_fresh_aux_symbol(
    signed_int_type(),
    CPROVER_PREFIX,
    symbol_name,
    source_locationt{},
    initialization_config.mode,
    goto_model.symbol_table);
  fresh_symbol.is_static_lifetime = true;
  fresh_symbol.is_lvalue = true;
  fresh_symbol.value = from_integer(0, signed_int_type());
  return fresh_symbol.symbol_expr();
}

symbol_exprt recursive_initializationt::get_fresh_local_symexpr(
  const std::string &symbol_name) const
{
  symbolt &fresh_symbol = get_fresh_aux_symbol(
    signed_int_type(),
    CPROVER_PREFIX,
    symbol_name,
    source_locationt{},
    initialization_config.mode,
    goto_model.symbol_table);
  fresh_symbol.is_lvalue = true;
  fresh_symbol.value = from_integer(0, signed_int_type());
  return fresh_symbol.symbol_expr();
}

symbol_exprt recursive_initializationt::get_fresh_local_typed_symexpr(
  const std::string &symbol_name,
  const typet &type,
  const exprt &init_value) const
{
  symbolt &fresh_symbol = get_fresh_aux_symbol(
    type,
    CPROVER_PREFIX,
    symbol_name,
    source_locationt{},
    initialization_config.mode,
    goto_model.symbol_table);
  fresh_symbol.is_lvalue = true;
  fresh_symbol.value = init_value;
  return fresh_symbol.symbol_expr();
}

const symbolt &recursive_initializationt::get_fresh_fun_symbol(
  const std::string &fun_name,
  const typet &fun_type)
{
  irep_idt fresh_name(fun_name);

  get_new_name(fresh_name, namespacet{goto_model.symbol_table}, '_');

  // create the function symbol
  symbolt function_symbol{};
  function_symbol.name = function_symbol.base_name =
    function_symbol.pretty_name = fresh_name;

  function_symbol.is_lvalue = true;
  function_symbol.mode = initialization_config.mode;
  function_symbol.type = fun_type;

  auto r = goto_model.symbol_table.insert(function_symbol);
  CHECK_RETURN(r.second);
  return *goto_model.symbol_table.lookup(fresh_name);
}

symbolt &recursive_initializationt::get_fresh_param_symbol(
  const std::string &symbol_name,
  const typet &symbol_type)
{
  symbolt &param_symbol = get_fresh_aux_symbol(
    symbol_type,
    CPROVER_PREFIX,
    symbol_name,
    source_locationt{},
    initialization_config.mode,
    goto_model.symbol_table);
  param_symbol.is_parameter = true;
  param_symbol.is_lvalue = true;

  return param_symbol;
}

symbol_exprt
recursive_initializationt::get_symbol_expr(const irep_idt &symbol_name) const
{
  auto maybe_symbol = goto_model.symbol_table.lookup(symbol_name);
  CHECK_RETURN(maybe_symbol != nullptr);
  return maybe_symbol->symbol_expr();
}

std::string recursive_initializationt::type2id(const typet &type) const
{
  if(type.id() == ID_struct_tag)
  {
    auto st_tag = id2string(to_struct_tag_type(type).get_identifier());
    std::replace(st_tag.begin(), st_tag.end(), '-', '_');
    return st_tag;
  }
  else if(type.id() == ID_pointer)
    return "ptr_" + type2id(type.subtype());
  else if(type.id() == ID_array)
  {
    const auto array_size =
      numeric_cast_v<std::size_t>(to_constant_expr(to_array_type(type).size()));
    return "arr_" + type2id(type.subtype()) + "_" + std::to_string(array_size);
  }
  else if(type == char_type())
    return "char";
  else if(type.id() == ID_signedbv)
    return "int";
  else if(type.id() == ID_unsignedbv)
    return "uint";
  else
    return "";
}

symbol_exprt recursive_initializationt::get_free_function()
{
  auto free_sym = goto_model.symbol_table.lookup("free");
  if(free_sym == nullptr)
  {
    symbolt new_free_sym;
    new_free_sym.type = code_typet{code_typet{
      {code_typet::parametert{pointer_type(empty_typet{})}}, empty_typet{}}};
    new_free_sym.name = new_free_sym.pretty_name = new_free_sym.base_name =
      "free";
    new_free_sym.mode = initialization_config.mode;
    goto_model.symbol_table.insert(new_free_sym);
    return new_free_sym.symbol_expr();
  }
  return free_sym->symbol_expr();
}

code_blockt recursive_initializationt::build_pointer_constructor(
  const exprt &depth,
  const exprt &result)
{
  PRECONDITION(result.type().id() == ID_pointer);
  const typet &type = result.type().subtype();
  PRECONDITION(type.id() == ID_pointer);

  code_blockt body{};

  // build:
  // void type_constructor_ptr_T(int depth, T** result)
  // {
  //   if(has_seen && depth >= max_depth)
  //     *result=NULL;
  //   else if(depth < min_null_tree_depth || nondet()) {
  //     size_t has_seen_prev;
  //     has_seen_prev = T_has_seen;
  //     T_has_seen = 1;
  //     *result = malloc(sizeof(T));
  //     type_constructor_T(depth+1, *result);
  //     T_has_seen=has_seen_prev;
  //   }
  //   else
  //     *result=NULL;
  // }

  binary_predicate_exprt depth_gt_max_depth{
    depth, ID_ge, get_symbol_expr(max_depth_var_name)};
  exprt::operandst should_not_recurse{depth_gt_max_depth};

  optionalt<symbol_exprt> has_seen;
  if(can_cast_type<struct_tag_typet>(type.subtype()))
    has_seen = get_fresh_global_symexpr("has_seen_" + type2id(type.subtype()));

  if(has_seen.has_value())
  {
    equal_exprt has_seen_expr{*has_seen, from_integer(1, has_seen->type())};
    should_not_recurse.push_back(has_seen_expr);
  }

  null_pointer_exprt nullptr_expr{pointer_type(type.subtype())};
  code_blockt null_and_return{};
  code_assignt assign_null{dereference_exprt{result}, nullptr_expr};
  null_and_return.add(assign_null);
  null_and_return.add(code_returnt{});
  body.add(code_ifthenelset{conjunction(should_not_recurse), null_and_return});

  exprt::operandst should_recurse_ops{
    binary_predicate_exprt{depth, ID_lt, get_symbol_expr(min_depth_var_name)},
    side_effect_expr_nondett{bool_typet{}, source_locationt{}}};
  code_blockt then_case{};

  code_assignt seen_assign_prev{};
  if(has_seen.has_value())
  {
    const symbol_exprt &has_seen_prev =
      get_fresh_local_symexpr("has_seen_prev_" + type2id(type.subtype()));
    then_case.add(code_declt{has_seen_prev});
    then_case.add(code_assignt{has_seen_prev, *has_seen});
    then_case.add(code_assignt{*has_seen, from_integer(1, has_seen->type())});
    seen_assign_prev = code_assignt{*has_seen, has_seen_prev};
  }

  const symbol_exprt &local_result =
    get_fresh_local_typed_symexpr("local_result", type, nullptr_expr);
  then_case.add(code_declt{local_result});
  const namespacet ns{goto_model.symbol_table};
  then_case.add(code_function_callt{
    local_result, get_malloc_function(), {*size_of_expr(type.subtype(), ns)}});
  initialize(
    dereference_exprt{local_result},
    plus_exprt{depth, from_integer(1, depth.type())},
    then_case);
  then_case.add(code_assignt{dereference_exprt{result}, local_result});

  if(has_seen.has_value())
  {
    then_case.add(seen_assign_prev);
  }

  body.add(
    code_ifthenelset{disjunction(should_recurse_ops), then_case, assign_null});
  return body;
}

code_blockt recursive_initializationt::build_array_string_constructor(
  const exprt &result) const
{
  PRECONDITION(result.type().id() == ID_pointer);
  const typet &type = result.type().subtype();
  PRECONDITION(type.id() == ID_array);
  PRECONDITION(type.subtype() == char_type());
  const array_typet &array_type = to_array_type(type);
  const auto array_size =
    numeric_cast_v<std::size_t>(to_constant_expr(array_type.size()));
  code_blockt body{};

  for(std::size_t index = 0; index < array_size - 1; index++)
  {
    index_exprt index_expr{dereference_exprt{result},
                           from_integer(index, size_type())};
    body.add(code_assignt{
      index_expr, side_effect_expr_nondett{char_type(), source_locationt{}}});
    body.add(code_assumet{
      notequal_exprt{index_expr, from_integer(0, array_type.subtype())}});
  }
  body.add(code_assignt{index_exprt{dereference_exprt{result},
                                    from_integer(array_size - 1, size_type())},
                        from_integer(0, array_type.subtype())});

  return body;
}

code_blockt recursive_initializationt::build_array_constructor(
  const exprt &depth,
  const exprt &result)
{
  PRECONDITION(result.type().id() == ID_pointer);
  const typet &type = result.type().subtype();
  PRECONDITION(type.id() == ID_array);
  const array_typet &array_type = to_array_type(type);
  const auto array_size =
    numeric_cast_v<std::size_t>(to_constant_expr(array_type.size()));
  code_blockt body{};

  for(std::size_t index = 0; index < array_size; index++)
  {
    initialize(
      index_exprt{dereference_exprt{result}, from_integer(index, size_type())},
      depth,
      body);
  }
  return body;
}

code_blockt recursive_initializationt::build_struct_constructor(
  const exprt &depth,
  const exprt &result)
{
  PRECONDITION(result.type().id() == ID_pointer);
  const typet &struct_type = result.type().subtype();
  PRECONDITION(struct_type.id() == ID_struct_tag);
  code_blockt body{};
  const namespacet ns{goto_model.symbol_table};
  for(const auto &component :
      ns.follow_tag(to_struct_tag_type(struct_type)).components())
  {
    initialize(member_exprt{dereference_exprt{result}, component}, depth, body);
  }
  return body;
}

code_blockt
recursive_initializationt::build_nondet_constructor(const exprt &result) const
{
  PRECONDITION(result.type().id() == ID_pointer);
  code_blockt body{};
  body.add(code_assignt{
    dereference_exprt{result},
    side_effect_expr_nondett{result.type().subtype(), source_locationt{}}});
  return body;
}

code_blockt recursive_initializationt::build_dynamic_array_constructor(
  const exprt &depth,
  const exprt &result,
  const exprt &size,
  const optionalt<irep_idt> &lhs_name)
{
  PRECONDITION(result.type().id() == ID_pointer);
  const typet &pointer_type = result.type().subtype();
  PRECONDITION(pointer_type.id() == ID_pointer);
  const typet &element_type = pointer_type.subtype();

  // builds:
  // void type_constructor_ptr_T(int depth, T** result, int* size)
  // {
  //   int nondet_size;
  //   assume(nondet_size >= min_array_size && nondet_size <= max_array_size);
  //   T* local_result = malloc(nondet_size * sizeof(T));
  //   for (int i = 0; i < nondet_size; ++i)
  //   {
  //     type_construct_T(depth+1, local_result+i);
  //   }
  //   *result = local_result;
  //   if (size!=NULL)
  //     *size = nondet_size;
  // }

  const auto min_array_size = initialization_config.min_dynamic_array_size;
  const auto max_array_size = initialization_config.max_dynamic_array_size;
  PRECONDITION(max_array_size >= min_array_size);

  code_blockt body{};
  const symbol_exprt &nondet_size = get_fresh_local_symexpr("nondet_size");
  body.add(code_declt{nondet_size});

  body.add(code_assumet{and_exprt{
    binary_relation_exprt{
      nondet_size, ID_ge, from_integer(min_array_size, nondet_size.type())},
    binary_relation_exprt{
      nondet_size, ID_le, from_integer(max_array_size, nondet_size.type())}}});

  const symbol_exprt &local_result =
    get_fresh_local_typed_symexpr("local_result", pointer_type, exprt{});
  body.add(code_declt{local_result});
  const namespacet ns{goto_model.symbol_table};
  for(auto array_size = min_array_size; array_size <= max_array_size;
      ++array_size)
  {
    body.add(code_ifthenelset{
      equal_exprt{nondet_size, from_integer(array_size, nondet_size.type())},
      code_function_callt{local_result,
                          get_malloc_function(),
                          {mult_exprt{from_integer(array_size, size_type()),
                                      *size_of_expr(element_type, ns)}}}});
  }

  const symbol_exprt &index_iter = get_fresh_local_symexpr("index");
  body.add(code_declt{index_iter});
  code_assignt for_init{index_iter, from_integer(0, index_iter.type())};
  binary_relation_exprt for_cond{index_iter, ID_lt, nondet_size};
  side_effect_exprt for_iter{
    ID_preincrement, {index_iter}, typet{}, source_locationt{}};
  code_blockt for_body{};
  if(lhs_name.has_value() && should_be_treated_as_cstring(*lhs_name))
  {
    code_blockt else_case{};
    initialize(
      dereference_exprt{plus_exprt{local_result, index_iter}},
      plus_exprt{depth, from_integer(1, depth.type())},
      else_case);
    else_case.add(code_assumet{
      notequal_exprt{dereference_exprt{plus_exprt{local_result, index_iter}},
                     from_integer(0, char_type())}});

    for_body.add(code_ifthenelset{
      equal_exprt{
        index_iter,
        minus_exprt{nondet_size, from_integer(1, nondet_size.type())}},
      code_assignt{dereference_exprt{plus_exprt{local_result, index_iter}},
                   from_integer(0, char_type())},
      else_case});
  }
  else
  {
    initialize(
      dereference_exprt{plus_exprt{local_result, index_iter}},
      plus_exprt{depth, from_integer(1, depth.type())},
      for_body);
  }

  body.add(code_fort{for_init, for_cond, for_iter, for_body});
  body.add(code_assignt{dereference_exprt{result}, local_result});

  CHECK_RETURN(size.type().id() == ID_pointer);
  body.add(code_ifthenelset{
    notequal_exprt{size, null_pointer_exprt{to_pointer_type(size.type())}},
    code_assignt{
      dereference_exprt{size},
      typecast_exprt::conditional_cast(nondet_size, size.type().subtype())}});

  return body;
}
