/******************************************************************\

Module: harness generator for functions

Author: Diffblue Ltd.

\******************************************************************/

#include "function_call_harness_generator.h"

#include <util/allocate_objects.h>
#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/exception_utils.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/string2int.h>
#include <util/string_utils.h>
#include <util/ui_message.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_model.h>

#include <algorithm>
#include <iterator>
#include <set>

#include "function_harness_generator_options.h"
#include "goto_harness_parse_options.h"
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
  /// declare local variables for each of the parameters of the entry function
  /// and return them
  code_function_callt::argumentst declare_arguments(code_blockt &function_body);
  /// write initialisation code for each of the arguments into function_body,
  /// then insert a call to the entry function with the arguments
  void call_function(
    const code_function_callt::argumentst &arguments,
    code_blockt &function_body);
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
  recursive_initialization_config.array_name_to_associated_array_size_variable =
    function_argument_to_associated_array_size;
  for(const auto &pair : function_argument_to_associated_array_size)
  {
    recursive_initialization_config.variables_that_hold_array_sizes.insert(
      pair.second);
  }
  recursive_initialization_config.pointers_to_treat_as_cstrings =
    function_arguments_to_treat_as_cstrings;
  recursive_initialization = util_make_unique<recursive_initializationt>(
    recursive_initialization_config, goto_model);

  generate_nondet_globals(function_body);
  call_function(arguments, function_body);
  for(const auto &global_pointer : global_pointers)
  {
    function_body.add(code_function_callt{
      recursive_initialization->get_free_function(), {global_pointer}});
  }
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
      if(recursive_initialization->is_initialization_allowed(symbol))
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
  if(lhs.type().id() == ID_pointer)
    global_pointers.insert(to_symbol_expr(lhs));
}

void function_call_harness_generatort::validate_options(
  const goto_modelt &goto_model)
{
  if(p_impl->function == ID_empty)
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

  auto const &generated_harness =
    symbol_table->lookup_ref(harness_function_name);
  goto_functions->function_map[harness_function_name].type =
    to_code_type(generated_harness.type);
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
      parameter.type(), parameter.get_base_name());
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
          "associated array size is not there",
          "--" FUNCTION_HARNESS_GENERATOR_ASSOCIATED_ARRAY_SIZE_OPT};
      }
      function_argument_to_associated_array_size.insert(
        {argument_name, associated_array_size_argument->second});
    }
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
    if(argument.type().id() == ID_pointer)
      global_pointers.insert(to_symbol_expr(argument));
  }
  code_function_callt function_call{function_to_call.symbol_expr(),
                                    std::move(arguments)};
  function_call.add_source_location() = function_to_call.location;

  function_body.add(std::move(function_call));
}
