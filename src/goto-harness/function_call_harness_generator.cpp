/******************************************************************\

Module: harness generator for functions

Author: Diffblue Ltd.

\******************************************************************/

#include "function_call_harness_generator.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/exception_utils.h>
#include <util/make_unique.h>
#include <util/prefix.h>
#include <util/std_code.h>
#include <util/string_utils.h>
#include <util/ui_message.h>

#include <goto-programs/allocate_objects.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_model.h>

#include <algorithm>
#include <iterator>
#include <set>

#include "function_harness_generator_options.h"
#include "goto_harness_generator_factory.h"
#include "recursive_initialization.h"

/// This contains implementation details of
/// function call harness generator to avoid
/// leaking them out into the header.
/* NOLINTNEXTLINE(readability/identifier_spacing) */
struct function_call_harness_generatort::implt
{
  ui_message_handlert *message_handler;
  irep_idt function;
  irep_idt harness_function_name;
  symbol_tablet *symbol_table;
  goto_functionst *goto_functions;
  bool nondet_globals = false;

  recursive_initialization_configt recursive_initialization_config;
  std::unique_ptr<recursive_initializationt> recursive_initialization;

  std::set<irep_idt> function_parameters_to_treat_as_arrays;
  std::set<irep_idt> function_arguments_to_treat_as_arrays;

  std::vector<std::set<irep_idt>> function_parameters_to_treat_equal;
  std::vector<std::set<irep_idt>> function_arguments_to_treat_equal;

  std::set<irep_idt> function_parameters_to_treat_as_cstrings;
  std::set<irep_idt> function_arguments_to_treat_as_cstrings;

  std::map<irep_idt, irep_idt> function_argument_to_associated_array_size;
  std::map<irep_idt, irep_idt> function_parameter_to_associated_array_size;

  std::set<symbol_exprt> global_pointers;

  /// \see goto_harness_generatort::generate
  void generate(goto_modelt &goto_model, const irep_idt &harness_function_name);
  /// Iterate over the symbol table and generate initialisation code for
  /// globals into the function body.
  void generate_nondet_globals(code_blockt &function_body);
  /// Return a reference to the entry function or throw if it doesn't exist.
  const symbolt &lookup_function_to_call();
  /// Generate initialisation code for one lvalue inside block.
  void generate_initialisation_code_for(code_blockt &block, const exprt &lhs);
  /// Throw if the harness function already exists in the symbol table.
  void ensure_harness_does_not_already_exist();
  /// Update the goto-model with the new harness function.
  void add_harness_function_to_goto_model(code_blockt function_body);
  /// Declare local variables for each of the parameters of the entry function
  /// and return them
  code_function_callt::argumentst declare_arguments(code_blockt &function_body);
  /// Write initialisation code for each of the arguments into function_body,
  /// then insert a call to the entry function with the arguments
  void call_function(
    const code_function_callt::argumentst &arguments,
    code_blockt &function_body);
  /// For function parameters that are pointers to functions we want to
  /// be able to specify whether or not they can be NULL. To disambiguate
  /// this specification from that for a global variable of the same name,
  /// we prepend the name of the function to the parameter name. However,
  /// what is actually being initialised in the implementation is not the
  /// parameter itself, but a corresponding function argument (local variable
  /// of the harness function). We need a mapping from function parameter
  /// name to function argument names, and this is what this function does.
  std::unordered_set<irep_idt>
  map_function_parameters_to_function_argument_names();
};

function_call_harness_generatort::function_call_harness_generatort(
  ui_message_handlert &message_handler)
  : goto_harness_generatort{}, p_impl(util_make_unique<implt>())
{
  p_impl->message_handler = &message_handler;
}

function_call_harness_generatort::~function_call_harness_generatort() = default;

void function_call_harness_generatort::handle_option(
  const std::string &option,
  const std::list<std::string> &values)
{
  auto &require_exactly_one_value =
    harness_options_parser::require_exactly_one_value;

  if(p_impl->recursive_initialization_config.handle_option(option, values))
  {
    // the option belongs to recursive initialization
  }
  else if(option == FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT)
  {
    p_impl->function = require_exactly_one_value(option, values);
  }
  else if(option == FUNCTION_HARNESS_GENERATOR_NONDET_GLOBALS_OPT)
  {
    p_impl->nondet_globals = true;
  }
  else if(option == FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_ARRAY_OPT)
  {
    p_impl->function_parameters_to_treat_as_arrays.insert(
      values.begin(), values.end());
  }
  else if(option == FUNCTION_HARNESS_GENERATOR_TREAT_POINTERS_EQUAL_OPT)
  {
    for(auto const &value : values)
    {
      for(auto const &param_cluster : split_string(value, ';'))
      {
        std::set<irep_idt> equal_param_set;
        for(auto const &param_id : split_string(param_cluster, ','))
        {
          equal_param_set.insert(param_id);
        }
        p_impl->function_parameters_to_treat_equal.push_back(equal_param_set);
      }
    }
  }
  else if(option == FUNCTION_HARNESS_GENERATOR_ASSOCIATED_ARRAY_SIZE_OPT)
  {
    for(auto const &array_size_pair : values)
    {
      try
      {
        std::string array;
        std::string size;
        split_string(array_size_pair, ':', array, size);
        // --associated-array-size implies --treat-pointer-as-array
        // but it is not an error to specify both, so we don't check
        // for duplicates here
        p_impl->function_parameters_to_treat_as_arrays.insert(array);
        auto const inserted =
          p_impl->function_parameter_to_associated_array_size.emplace(
            array, size);
        if(!inserted.second)
        {
          throw invalid_command_line_argument_exceptiont{
            "can not have two associated array sizes for one array",
            "--" FUNCTION_HARNESS_GENERATOR_ASSOCIATED_ARRAY_SIZE_OPT};
        }
      }
      catch(const deserialization_exceptiont &)
      {
        throw invalid_command_line_argument_exceptiont{
          "'" + array_size_pair +
            "' is in an invalid format for array size pair",
          "--" FUNCTION_HARNESS_GENERATOR_ASSOCIATED_ARRAY_SIZE_OPT,
          "array_name:size_name, where both are the names of function "
          "parameters"};
      }
    }
  }
  else if(option == FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_CSTRING)
  {
    p_impl->function_parameters_to_treat_as_cstrings.insert(
      values.begin(), values.end());
  }
  else if(option == FUNCTION_HARNESS_GENERATOR_TREAT_POINTERS_EQUAL_MAYBE_OPT)
  {
    p_impl->recursive_initialization_config.arguments_may_be_equal = true;
  }
  else if(option == COMMON_HARNESS_GENERATOR_FUNCTION_POINTER_CAN_BE_NULL_OPT)
  {
    std::transform(
      values.begin(),
      values.end(),
      std::inserter(
        p_impl->recursive_initialization_config
          .potential_null_function_pointers,
        p_impl->recursive_initialization_config.potential_null_function_pointers
          .end()),
      [](const std::string &opt) -> irep_idt { return irep_idt{opt}; });
  }
  else if(option == COMMON_HARNESS_GENERATOR_FUNCTION_POINTER_CAN_BE_NULL_OPT)
  {
    std::transform(
      values.begin(),
      values.end(),
      std::inserter(
        p_impl->recursive_initialization_config
          .potential_null_function_pointers,
        p_impl->recursive_initialization_config.potential_null_function_pointers
          .end()),
      [](const std::string &opt) -> irep_idt { return irep_idt{opt}; });
  }
  else
  {
    throw invalid_command_line_argument_exceptiont{
      "function harness generator cannot handle this option", "--" + option};
  }
}

void function_call_harness_generatort::generate(
  goto_modelt &goto_model,
  const irep_idt &harness_function_name)
{
  p_impl->generate(goto_model, harness_function_name);
}

void function_call_harness_generatort::implt::generate(
  goto_modelt &goto_model,
  const irep_idt &harness_function_name)
{
  symbol_table = &goto_model.symbol_table;
  goto_functions = &goto_model.goto_functions;
  this->harness_function_name = harness_function_name;
  const auto &function_to_call = lookup_function_to_call();
  ensure_harness_does_not_already_exist();

  // create body for the function
  code_blockt function_body{};
  auto const arguments = declare_arguments(function_body);

  // configure and create recursive initialisation object
  recursive_initialization_config.mode = function_to_call.mode;
  recursive_initialization_config.pointers_to_treat_as_arrays =
    function_arguments_to_treat_as_arrays;
  recursive_initialization_config.pointers_to_treat_equal =
    function_arguments_to_treat_equal;
  recursive_initialization_config.array_name_to_associated_array_size_variable =
    function_argument_to_associated_array_size;
  for(const auto &pair : function_argument_to_associated_array_size)
  {
    recursive_initialization_config.variables_that_hold_array_sizes.insert(
      pair.second);
  }
  recursive_initialization_config.potential_null_function_pointers =
    map_function_parameters_to_function_argument_names();
  recursive_initialization_config.pointers_to_treat_as_cstrings =
    function_arguments_to_treat_as_cstrings;
  recursive_initialization = util_make_unique<recursive_initializationt>(
    recursive_initialization_config, goto_model);

  generate_nondet_globals(function_body);
  call_function(arguments, function_body);
  for(const auto &global_pointer : global_pointers)
  {
    recursive_initialization->free_if_possible(global_pointer, function_body);
  }
  recursive_initialization->free_cluster_origins(function_body);
  add_harness_function_to_goto_model(std::move(function_body));
}

void function_call_harness_generatort::implt::generate_nondet_globals(
  code_blockt &function_body)
{
  if(nondet_globals)
  {
    // generating initialisation code may introduce new globals
    // i.e. modify the symbol table.
    // Modifying the symbol table while iterating over it is not
    // a good idea, therefore we just collect the names of globals
    // we need to initialise first and then generate the
    // initialisation code for all of them.
    auto globals = std::vector<symbol_exprt>{};
    for(const auto &symbol_table_entry : *symbol_table)
    {
      const auto &symbol = symbol_table_entry.second;
      if(recursive_initializationt::is_initialization_allowed(symbol))
      {
        globals.push_back(symbol.symbol_expr());
      }
    }
    for(auto const &global : globals)
    {
      generate_initialisation_code_for(function_body, global);
    }
  }
}

void function_call_harness_generatort::implt::generate_initialisation_code_for(
  code_blockt &block,
  const exprt &lhs)
{
  recursive_initialization->initialize(
    lhs, from_integer(0, signed_int_type()), block);
  if(recursive_initialization->needs_freeing(lhs))
    global_pointers.insert(to_symbol_expr(lhs));
}

void function_call_harness_generatort::validate_options(
  const goto_modelt &goto_model)
{
  if(p_impl->function == ID_empty_string)
    throw invalid_command_line_argument_exceptiont{
      "required parameter entry function not set",
      "--" FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT};
  if(
    p_impl->recursive_initialization_config.min_dynamic_array_size >
    p_impl->recursive_initialization_config.max_dynamic_array_size)
  {
    throw invalid_command_line_argument_exceptiont{
      "min dynamic array size cannot be greater than max dynamic array size",
      "--" COMMON_HARNESS_GENERATOR_MIN_ARRAY_SIZE_OPT
      " --" COMMON_HARNESS_GENERATOR_MAX_ARRAY_SIZE_OPT};
  }

  const auto function_to_call_pointer =
    goto_model.symbol_table.lookup(p_impl->function);
  if(function_to_call_pointer == nullptr)
  {
    throw invalid_command_line_argument_exceptiont{
      "entry function `" + id2string(p_impl->function) +
        "' does not exist in the symbol table",
      "--" FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT};
  }
  const auto &function_to_call = *function_to_call_pointer;
  const auto &ftype = to_code_type(function_to_call.type);
  for(auto const &equal_cluster : p_impl->function_parameters_to_treat_equal)
  {
    for(auto const &pointer_id : equal_cluster)
    {
      std::string decorated_pointer_id =
        id2string(p_impl->function) + "::" + id2string(pointer_id);
      bool is_a_param = false;
      typet common_type = empty_typet{};
      for(auto const &formal_param : ftype.parameters())
      {
        if(formal_param.get_identifier() == decorated_pointer_id)
        {
          is_a_param = true;
          if(formal_param.type().id() != ID_pointer)
          {
            throw invalid_command_line_argument_exceptiont{
              id2string(pointer_id) + " is not a pointer parameter",
              "--" FUNCTION_HARNESS_GENERATOR_TREAT_POINTERS_EQUAL_OPT};
          }
          if(common_type.id() != ID_empty)
          {
            if(common_type != formal_param.type())
            {
              throw invalid_command_line_argument_exceptiont{
                "pointer arguments of conflicting type",
                "--" FUNCTION_HARNESS_GENERATOR_TREAT_POINTERS_EQUAL_OPT};
            }
          }
          else
            common_type = formal_param.type();
        }
      }
      if(!is_a_param)
      {
        throw invalid_command_line_argument_exceptiont{
          id2string(pointer_id) + " is not a parameter",
          "--" FUNCTION_HARNESS_GENERATOR_TREAT_POINTERS_EQUAL_OPT};
      }
    }
  }

  const namespacet ns{goto_model.symbol_table};

  // Make sure all function pointers that the user asks are nullable are
  // present in the symbol table.
  for(const auto &nullable :
      p_impl->recursive_initialization_config.potential_null_function_pointers)
  {
    const auto &function_pointer_symbol_pointer =
      goto_model.symbol_table.lookup(nullable);

    if(function_pointer_symbol_pointer == nullptr)
    {
      throw invalid_command_line_argument_exceptiont{
        "nullable function pointer `" + id2string(nullable) +
          "' not found in symbol table",
        "--" COMMON_HARNESS_GENERATOR_FUNCTION_POINTER_CAN_BE_NULL_OPT};
    }

    const auto &function_pointer_type =
      ns.follow(function_pointer_symbol_pointer->type);

    if(!can_cast_type<pointer_typet>(function_pointer_type))
    {
      throw invalid_command_line_argument_exceptiont{
        "`" + id2string(nullable) + "' is not a pointer",
        "--" COMMON_HARNESS_GENERATOR_FUNCTION_POINTER_CAN_BE_NULL_OPT};
    }

    if(!can_cast_type<code_typet>(
         to_pointer_type(function_pointer_type).subtype()))
    {
      throw invalid_command_line_argument_exceptiont{
        "`" + id2string(nullable) + "' is not pointing to a function",
        "--" COMMON_HARNESS_GENERATOR_FUNCTION_POINTER_CAN_BE_NULL_OPT};
    }
  }
}

const symbolt &
function_call_harness_generatort::implt::lookup_function_to_call()
{
  auto function_found = symbol_table->lookup(function);

  if(function_found == nullptr)
  {
    throw invalid_command_line_argument_exceptiont{
      "function that should be harnessed is not found " + id2string(function),
      "--" FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT};
  }

  return *function_found;
}

void function_call_harness_generatort::implt::
  ensure_harness_does_not_already_exist()
{
  if(symbol_table->lookup(harness_function_name))
  {
    throw invalid_command_line_argument_exceptiont{
      "harness function already exists in the symbol table",
      "--" GOTO_HARNESS_GENERATOR_HARNESS_FUNCTION_NAME_OPT};
  }
}

void function_call_harness_generatort::implt::
  add_harness_function_to_goto_model(code_blockt function_body)
{
  const auto &function_to_call = lookup_function_to_call();

  // create the function symbol
  symbolt harness_function_symbol{};
  harness_function_symbol.name = harness_function_symbol.base_name =
    harness_function_symbol.pretty_name = harness_function_name;

  harness_function_symbol.is_lvalue = true;
  harness_function_symbol.mode = function_to_call.mode;
  harness_function_symbol.type = code_typet{{}, empty_typet{}};
  harness_function_symbol.value = std::move(function_body);

  symbol_table->insert(harness_function_symbol);

  goto_convert(*symbol_table, *goto_functions, *message_handler);
}

code_function_callt::argumentst
function_call_harness_generatort::implt::declare_arguments(
  code_blockt &function_body)
{
  const auto &function_to_call = lookup_function_to_call();
  const auto &function_type = to_code_type(function_to_call.type);
  const auto &parameters = function_type.parameters();

  code_function_callt::operandst arguments{};

  auto allocate_objects = allocate_objectst{function_to_call.mode,
                                            function_to_call.location,
                                            "__goto_harness",
                                            *symbol_table};
  std::map<irep_idt, irep_idt> parameter_name_to_argument_name;
  for(const auto &parameter : parameters)
  {
    auto argument = allocate_objects.allocate_automatic_local_object(
      remove_const(parameter.type()), parameter.get_base_name());
    parameter_name_to_argument_name.insert(
      {parameter.get_base_name(), argument.get_identifier()});
    arguments.push_back(argument);
  }

  for(const auto &pair : parameter_name_to_argument_name)
  {
    auto const &parameter_name = pair.first;
    auto const &argument_name = pair.second;
    if(function_parameters_to_treat_as_arrays.count(parameter_name) != 0)
    {
      function_arguments_to_treat_as_arrays.insert(argument_name);
    }

    if(function_parameters_to_treat_as_cstrings.count(parameter_name) != 0)
    {
      function_arguments_to_treat_as_cstrings.insert(argument_name);
    }

    auto it = function_parameter_to_associated_array_size.find(parameter_name);
    if(it != function_parameter_to_associated_array_size.end())
    {
      auto const &associated_array_size_parameter = it->second;
      auto associated_array_size_argument =
        parameter_name_to_argument_name.find(associated_array_size_parameter);
      if(
        associated_array_size_argument == parameter_name_to_argument_name.end())
      {
        throw invalid_command_line_argument_exceptiont{
          "could not find parameter to associate the array size of array \"" +
            id2string(parameter_name) + "\" (Expected parameter: \"" +
            id2string(associated_array_size_parameter) + "\" on function \"" +
            id2string(function_to_call.display_name()) + "\" in " +
            function_to_call.location.as_string() + ")",
          "--" FUNCTION_HARNESS_GENERATOR_ASSOCIATED_ARRAY_SIZE_OPT};
      }
      function_argument_to_associated_array_size.insert(
        {argument_name, associated_array_size_argument->second});
    }
  }

  // translate the parameter to argument also in the equality clusters
  for(auto const &equal_cluster : function_parameters_to_treat_equal)
  {
    std::set<irep_idt> cluster_argument_names;
    for(auto const &parameter_name : equal_cluster)
    {
      INVARIANT(
        parameter_name_to_argument_name.count(parameter_name) != 0,
        id2string(parameter_name) + " is not a parameter");
      cluster_argument_names.insert(
        parameter_name_to_argument_name[parameter_name]);
    }
    function_arguments_to_treat_equal.push_back(cluster_argument_names);
  }

  allocate_objects.declare_created_symbols(function_body);
  return arguments;
}

void function_call_harness_generatort::implt::call_function(
  const code_function_callt::argumentst &arguments,
  code_blockt &function_body)
{
  auto const &function_to_call = lookup_function_to_call();
  for(auto const &argument : arguments)
  {
    generate_initialisation_code_for(function_body, argument);
    if(recursive_initialization->needs_freeing(argument))
      global_pointers.insert(to_symbol_expr(argument));
  }
  code_function_callt function_call{function_to_call.symbol_expr(),
                                    std::move(arguments)};
  function_call.add_source_location() = function_to_call.location;

  function_body.add(std::move(function_call));
}

std::unordered_set<irep_idt> function_call_harness_generatort::implt::
  map_function_parameters_to_function_argument_names()
{
  std::unordered_set<irep_idt> nullables;
  for(const auto &nullable :
      recursive_initialization_config.potential_null_function_pointers)
  {
    const auto &nullable_name = id2string(nullable);
    const auto &function_prefix = id2string(function) + "::";
    if(has_prefix(nullable_name, function_prefix))
    {
      nullables.insert(
        "__goto_harness::" + nullable_name.substr(function_prefix.size()));
    }
    else
    {
      nullables.insert(nullable_name);
    }
  }
  return nullables;
}
