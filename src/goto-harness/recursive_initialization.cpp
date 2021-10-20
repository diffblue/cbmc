/******************************************************************\

Module: recursive_initialization

Author: Diffblue Ltd.

\******************************************************************/

#include "recursive_initialization.h"

#include <goto-programs/name_mangler.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/fresh_symbol.h>
#include <util/irep.h>
#include <util/optional_utils.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/rename.h>
#include <util/std_code.h>
#include <util/string2int.h>
#include <util/string_utils.h>

#include <iterator>

#include "common_harness_generator_options.h"
#include "goto_harness_generator.h"

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
  else if(option == COMMON_HARNESS_GENERATOR_FUNCTION_POINTER_CAN_BE_NULL_OPT)
  {
    std::transform(
      values.begin(),
      values.end(),
      std::inserter(
        potential_null_function_pointers,
        potential_null_function_pointers.end()),
      [](const std::string &opt) -> irep_idt { return irep_idt{opt}; });
    return true;
  }
  else if(option == COMMON_HARNESS_GENERATOR_HAVOC_MEMBER_OPT)
  {
    const auto list_of_members_string =
      harness_options_parser::require_exactly_one_value(
        COMMON_HARNESS_GENERATOR_HAVOC_MEMBER_OPT, values);
    const auto list_of_members = split_string(list_of_members_string, ',');
    for(const auto &member : list_of_members)
    {
      const auto selection_spec_strings = split_string(member, '.');

      selection_specs.push_back({});
      auto &selection_spec = selection_specs.back();
      std::transform(
        selection_spec_strings.begin(),
        selection_spec_strings.end(),
        std::back_inserter(selection_spec),
        [](const std::string &member_name_string) {
          return irep_idt{member_name_string};
        });
    }
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
  common_arguments_origins.resize(
    this->initialization_config.pointers_to_treat_equal.size());
}

void recursive_initializationt::initialize(
  const exprt &lhs,
  const exprt &depth,
  code_blockt &body)
{
  if(lhs.id() == ID_symbol && !initialization_config.selection_specs.empty())
  {
    auto lhs_id = to_symbol_expr(lhs).get_identifier();
    for(const auto &selection_spec : initialization_config.selection_specs)
    {
      if(selection_spec.front() == lhs_id)
      {
        initialize_selected_member(lhs, depth, body, selection_spec);
        return;
      }
    }
  }
  // special handling for the case that pointer arguments should be treated
  // equal: if the equality is enforced (rather than the pointers may be equal),
  // then we don't even build the constructor functions
  if(lhs.id() == ID_symbol)
  {
    const auto maybe_cluster_index =
      find_equal_cluster(to_symbol_expr(lhs).get_identifier());
    if(maybe_cluster_index.has_value())
    {
      if(common_arguments_origins[*maybe_cluster_index].has_value())
      {
        const auto set_equal_case =
          code_assignt{lhs, *common_arguments_origins[*maybe_cluster_index]};
        if(initialization_config.arguments_may_be_equal)
        {
          const irep_idt &fun_name = build_constructor(lhs);
          const symbolt &fun_symbol =
            goto_model.symbol_table.lookup_ref(fun_name);
          const auto proper_init_case = code_function_callt{
            fun_symbol.symbol_expr(), {depth, address_of_exprt{lhs}}};
          const auto should_make_equal =
            get_fresh_local_typed_symexpr("should_make_equal", bool_typet{});
          body.add(code_declt{should_make_equal});
          body.add(code_ifthenelset{
            should_make_equal, set_equal_case, proper_init_case});
        }
        else
        {
          body.add(set_equal_case);
        }
        return;
      }
      else
      {
        common_arguments_origins[*maybe_cluster_index] = lhs;
      }
    }
  }

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
        const pointer_typet *size_var_type =
          type_try_dynamic_cast<pointer_typet>(fun_type_params.back().type());
        INVARIANT(size_var_type, "Size parameter must have pointer type.");
        body.add(code_function_callt{
          fun_symbol.symbol_expr(),
          {depth, address_of_exprt{lhs}, null_pointer_exprt{*size_var_type}}});
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

code_blockt build_null_pointer(const symbol_exprt &result_symbol)
{
  const typet &type_to_construct = result_symbol.type().subtype();
  const null_pointer_exprt nullptr_expr{to_pointer_type(type_to_construct)};
  const code_assignt assign_null{dereference_exprt{result_symbol},
                                 nullptr_expr};
  return code_blockt{{assign_null, code_frontend_returnt{}}};
}

code_blockt recursive_initializationt::build_constructor_body(
  const exprt &depth_symbol,
  const symbol_exprt &result_symbol,
  const optionalt<exprt> &size_symbol,
  const optionalt<irep_idt> &lhs_name,
  const bool is_nullable)
{
  PRECONDITION(result_symbol.type().id() == ID_pointer);
  const typet &type = result_symbol.type().subtype();
  if(type.id() == ID_struct_tag)
  {
    return build_struct_constructor(depth_symbol, result_symbol);
  }
  else if(type.id() == ID_pointer)
  {
    if(type.subtype().id() == ID_code)
    {
      return build_function_pointer_constructor(result_symbol, is_nullable);
    }
    if(type.subtype().id() == ID_empty)
    {
      // always initalize void* pointers as NULL
      return build_null_pointer(result_symbol);
    }
    if(lhs_name.has_value())
    {
      if(should_be_treated_as_array(*lhs_name))
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

irep_idt recursive_initializationt::build_constructor(const exprt &expr)
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
  bool is_nullable = false;
  bool has_size_param = false;
  if(expr.id() == ID_symbol)
  {
    expr_name = to_symbol_expr(expr).get_identifier();
    is_nullable = initialization_config.potential_null_function_pointers.count(
      expr_name.value());
    if(should_be_treated_as_array(*expr_name))
    {
      size_var = get_associated_size_variable(*expr_name);
      has_size_param = true;
    }
  }
  const typet &type = expr.type();
  const constructor_keyt key{type, is_nullable, has_size_param};
  if(type_constructor_names.find(key) != type_constructor_names.end())
    return type_constructor_names[key];

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
  type_constructor_names[key] = function_symbol.name;
  symbolt *mutable_symbol = symbol_table.get_writeable(function_symbol.name);

  // the body is specific for each type of expression
  mutable_symbol->value = build_constructor_body(
    depth_symbol.symbol_expr(),
    result_symbol.symbol_expr(),
    size_symbol_expr,
    // the expression name may be needed to decide if expr should be treated as
    // a string
    expr_name,
    is_nullable);

  return type_constructor_names.at(key);
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

optionalt<recursive_initializationt::equal_cluster_idt>
recursive_initializationt::find_equal_cluster(const irep_idt &name) const
{
  for(equal_cluster_idt index = 0;
      index != initialization_config.pointers_to_treat_equal.size();
      ++index)
  {
    if(initialization_config.pointers_to_treat_equal[index].count(name) != 0)
      return index;
  }
  return {};
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

static symbolt &get_fresh_global_symbol(
  symbol_tablet &symbol_table,
  const std::string &symbol_base_name,
  typet symbol_type,
  irep_idt mode)
{
  source_locationt source_location{};
  source_location.set_file(GOTO_HARNESS_PREFIX "harness.c");
  symbolt &fresh_symbol = get_fresh_aux_symbol(
    std::move(symbol_type),
    GOTO_HARNESS_PREFIX,
    symbol_base_name,
    source_locationt{},
    mode,
    symbol_table);
  fresh_symbol.base_name = fresh_symbol.pretty_name = symbol_base_name;
  fresh_symbol.is_static_lifetime = true;
  fresh_symbol.is_lvalue = true;
  fresh_symbol.is_auxiliary = false;
  fresh_symbol.is_file_local = false;
  fresh_symbol.is_thread_local = false;
  fresh_symbol.is_state_var = false;
  fresh_symbol.module = GOTO_HARNESS_PREFIX "harness";
  fresh_symbol.location = std::move(source_location);
  return fresh_symbol;
}

irep_idt recursive_initializationt::get_fresh_global_name(
  const std::string &symbol_name,
  const exprt &initial_value) const
{
  auto &fresh_symbol = get_fresh_global_symbol(
    goto_model.symbol_table,
    symbol_name,
    signed_int_type(), // FIXME why always signed_int_type???
    initialization_config.mode);
  fresh_symbol.value = initial_value;
  return fresh_symbol.name;
}

symbol_exprt recursive_initializationt::get_fresh_global_symexpr(
  const std::string &symbol_name) const
{
  auto &fresh_symbol = get_fresh_global_symbol(
    goto_model.symbol_table,
    symbol_name,
    signed_int_type(),
    initialization_config.mode);
  fresh_symbol.value = from_integer(0, signed_int_type());
  return fresh_symbol.symbol_expr();
}

symbol_exprt recursive_initializationt::get_fresh_local_symexpr(
  const std::string &symbol_name) const
{
  symbolt &fresh_symbol = get_fresh_aux_symbol(
    signed_int_type(),
    GOTO_HARNESS_PREFIX,
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
  const typet &type) const
{
  symbolt &fresh_symbol = get_fresh_aux_symbol(
    type,
    GOTO_HARNESS_PREFIX,
    symbol_name,
    source_locationt{},
    initialization_config.mode,
    goto_model.symbol_table);
  fresh_symbol.is_lvalue = true;
  fresh_symbol.mode = initialization_config.mode;
  return fresh_symbol.symbol_expr();
}

const symbolt &recursive_initializationt::get_fresh_fun_symbol(
  const std::string &fun_name,
  const typet &fun_type)
{
  irep_idt fresh_name =
    get_new_name(fun_name, namespacet{goto_model.symbol_table}, '_');

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
    GOTO_HARNESS_PREFIX,
    symbol_name,
    source_locationt{},
    initialization_config.mode,
    goto_model.symbol_table);
  param_symbol.is_parameter = true;
  param_symbol.is_lvalue = true;
  param_symbol.mode = initialization_config.mode;

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
  const symbol_exprt &result)
{
  PRECONDITION(result.type().id() == ID_pointer);
  const typet &type = result.type().subtype();
  PRECONDITION(type.id() == ID_pointer);
  PRECONDITION(type.subtype().id() != ID_empty);

  code_blockt body{};
  // build:
  // void type_constructor_ptr_T(int depth, T** result)
  // {
  //   if(has_seen && depth >= max_depth)
  //     *result=NULL;
  //     return
  //   if(nondet()) {
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
  const code_assignt assign_null{dereference_exprt{result}, nullptr_expr};
  code_blockt null_and_return{{assign_null, code_frontend_returnt{}}};
  body.add(code_ifthenelset{conjunction(should_not_recurse), null_and_return});

  const auto should_recurse_nondet =
    get_fresh_local_typed_symexpr("should_recurse_nondet", bool_typet{});
  body.add(code_declt{should_recurse_nondet});
  exprt::operandst should_recurse_ops{
    binary_predicate_exprt{depth, ID_lt, get_symbol_expr(min_depth_var_name)},
    should_recurse_nondet};
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

  // we want to initialize the pointee as non-const even for pointer to const
  const typet non_const_pointer_type =
    pointer_type(remove_const(type.subtype()));
  const symbol_exprt &local_result =
    get_fresh_local_typed_symexpr("local_result", non_const_pointer_type);

  then_case.add(code_declt{local_result});
  const namespacet ns{goto_model.symbol_table};
  then_case.add(
    code_function_callt{local_result,
                        get_malloc_function(),
                        {*size_of_expr(non_const_pointer_type.subtype(), ns)}});
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

code_blockt recursive_initializationt::build_array_constructor(
  const exprt &depth,
  const symbol_exprt &result)
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
  const symbol_exprt &result)
{
  PRECONDITION(result.type().id() == ID_pointer);
  const typet &struct_type = result.type().subtype();
  PRECONDITION(struct_type.id() == ID_struct_tag);
  code_blockt body{};
  const namespacet ns{goto_model.symbol_table};
  for(const auto &component :
      ns.follow_tag(to_struct_tag_type(struct_type)).components())
  {
    if(component.get_is_padding())
    {
      continue;
    }
    // if the struct component is const we need to cast away the const
    // for initialisation purposes.
    // As far as I'm aware that's the closest thing to a 'correct' way
    // to initialize dynamically allocated structs with const components
    exprt component_initialisation_lhs = [&result, &component]() -> exprt {
      auto member_expr = member_exprt{dereference_exprt{result}, component};
      if(component.type().get_bool(ID_C_constant))
      {
        return dereference_exprt{
          typecast_exprt{address_of_exprt{std::move(member_expr)},
                         pointer_type(remove_const(component.type()))}};
      }
      else
      {
        return std::move(member_expr);
      }
    }();
    initialize(component_initialisation_lhs, depth, body);
  }
  return body;
}

code_blockt recursive_initializationt::build_nondet_constructor(
  const symbol_exprt &result) const
{
  PRECONDITION(result.type().id() == ID_pointer);
  code_blockt body{};
  auto const nondet_symbol =
    get_fresh_local_typed_symexpr("nondet", result.type().subtype());
  body.add(code_declt{nondet_symbol});
  body.add(code_assignt{dereference_exprt{result}, nondet_symbol});
  return body;
}

code_blockt recursive_initializationt::build_dynamic_array_constructor(
  const exprt &depth,
  const symbol_exprt &result,
  const exprt &size,
  const optionalt<irep_idt> &lhs_name)
{
  PRECONDITION(result.type().id() == ID_pointer);
  const typet &dynamic_array_type = result.type().subtype();
  PRECONDITION(dynamic_array_type.id() == ID_pointer);
  const typet &element_type = dynamic_array_type.subtype();
  PRECONDITION(element_type.id() != ID_empty);

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

  // we want the local result to be mutable so we can initialise it
  const typet mutable_dynamic_array_type =
    pointer_type(remove_const(element_type));
  const symbol_exprt &local_result =
    get_fresh_local_typed_symexpr("local_result", mutable_dynamic_array_type);
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

bool recursive_initializationt::needs_freeing(const exprt &expr) const
{
  if(expr.type().id() != ID_pointer || expr.type().subtype().id() == ID_code)
    return false;
  for(auto const &common_arguments_origin : common_arguments_origins)
  {
    if(common_arguments_origin.has_value() && expr.id() == ID_symbol)
    {
      auto origin_name =
        to_symbol_expr(*common_arguments_origin).get_identifier();
      auto expr_name = to_symbol_expr(expr).get_identifier();
      return origin_name == expr_name;
    }
  }
  return true;
}

void recursive_initializationt::free_if_possible(
  const exprt &expr,
  code_blockt &body)
{
  PRECONDITION(expr.id() == ID_symbol);
  const auto expr_id = to_symbol_expr(expr).get_identifier();
  const auto maybe_cluster_index = find_equal_cluster(expr_id);
  const auto call_free = code_function_callt{get_free_function(), {expr}};
  if(!maybe_cluster_index.has_value())
  {
    // not in any equality cluster -> just free
    body.add(call_free);
    return;
  }

  if(
    to_symbol_expr(*common_arguments_origins[*maybe_cluster_index])
        .get_identifier() != expr_id &&
    initialization_config.arguments_may_be_equal)
  {
    // in equality cluster but not common origin -> free if not equal to origin
    const auto condition =
      notequal_exprt{expr, *common_arguments_origins[*maybe_cluster_index]};
    body.add(code_ifthenelset{condition, call_free});
  }
  else
  {
    // expr is common origin, leave freeing until the rest of the cluster is
    // freed
    return;
  }
}

void recursive_initializationt::free_cluster_origins(code_blockt &body)
{
  for(auto const &origin : common_arguments_origins)
  {
    body.add(code_function_callt{get_free_function(), {*origin}});
  }
}

code_blockt recursive_initializationt::build_function_pointer_constructor(
  const symbol_exprt &result,
  bool is_nullable)
{
  PRECONDITION(can_cast_type<pointer_typet>(result.type()));
  const auto &result_type = to_pointer_type(result.type());
  PRECONDITION(can_cast_type<pointer_typet>(result_type.subtype()));
  const auto &function_pointer_type = to_pointer_type(result_type.subtype());
  PRECONDITION(can_cast_type<code_typet>(function_pointer_type.subtype()));
  const auto &function_type = to_code_type(function_pointer_type.subtype());

  std::vector<exprt> targets;

  for(const auto &sym : goto_model.get_symbol_table())
  {
    if(sym.second.type == function_type)
    {
      targets.push_back(address_of_exprt{sym.second.symbol_expr()});
    }
  }

  if(is_nullable)
    targets.push_back(null_pointer_exprt{function_pointer_type});

  code_blockt body{};

  const auto function_pointer_selector =
    get_fresh_local_symexpr("function_pointer_selector");
  body.add(code_declt{function_pointer_selector});
  auto function_pointer_index = std::size_t{0};

  for(const auto &target : targets)
  {
    auto const assign = code_assignt{dereference_exprt{result}, target};
    auto const sym_to_lookup =
      target.id() == ID_address_of
        ?
        // This is either address of or pointer; in pointer case, we don't
        // need to do anything. In the address of case, the operand is
        // a symbol representing a target function.
        to_symbol_expr(to_address_of_expr(target).object()).get_identifier()
        : "";
    // skip referencing globals because the corresponding symbols in the symbol
    // table are no longer marked as file local.
    if(has_prefix(id2string(sym_to_lookup), FILE_LOCAL_PREFIX))
    {
      continue;
    }
    else if(
      goto_model.get_symbol_table().lookup(sym_to_lookup) &&
      goto_model.get_symbol_table().lookup(sym_to_lookup)->is_file_local)
    {
      continue;
    }

    if(function_pointer_index != targets.size() - 1)
    {
      auto const condition = equal_exprt{
        function_pointer_selector,
        from_integer(function_pointer_index, function_pointer_selector.type())};
      auto const then = code_blockt{{assign, code_frontend_returnt{}}};
      body.add(code_ifthenelset{condition, then});
    }
    else
    {
      body.add(assign);
    }
    ++function_pointer_index;
  }

  return body;
}

void recursive_initializationt::initialize_selected_member(
  const exprt &lhs,
  const exprt &depth,
  code_blockt &body,
  const std::vector<irep_idt> &selection_spec)
{
  PRECONDITION(lhs.id() == ID_symbol);
  PRECONDITION(lhs.type().id() == ID_struct_tag);
  PRECONDITION(!selection_spec.empty());

  auto component_member = lhs;
  const namespacet ns{goto_model.symbol_table};

  for(auto it = selection_spec.begin() + 1; it != selection_spec.end(); it++)
  {
    if(component_member.type().id() != ID_struct_tag)
    {
      throw invalid_command_line_argument_exceptiont{
        "'" + id2string(*it) + "' is not a component name",
        "--" COMMON_HARNESS_GENERATOR_HAVOC_MEMBER_OPT};
    }
    const auto &struct_tag_type = to_struct_tag_type(component_member.type());
    const auto &struct_type = to_struct_type(ns.follow_tag(struct_tag_type));

    bool found = false;
    for(auto const &component : struct_type.components())
    {
      const auto &component_type = component.type();
      const auto component_name = component.get_name();

      if(*it == component_name)
      {
        component_member =
          member_exprt{component_member, component_name, component_type};
        found = true;
        break;
      }
    }
    if(!found)
    {
      throw invalid_command_line_argument_exceptiont{
        "'" + id2string(*it) + "' is not a component name",
        "--" COMMON_HARNESS_GENERATOR_HAVOC_MEMBER_OPT};
    }
  }
  initialize(component_member, depth, body);
}
