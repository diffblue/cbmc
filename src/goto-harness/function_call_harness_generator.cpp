/******************************************************************\

Module: harness generator for functions

Author: Diffblue Ltd.

\******************************************************************/

#include "function_call_harness_generator.h"

#include <goto-programs/goto_convert.h>
#include <goto-programs/goto_model.h>
#include <util/allocate_objects.h>
#include <util/exception_utils.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/ui_message.h>

#include "function_harness_generator_options.h"
#include "goto_harness_parse_options.h"

struct function_call_harness_generatort::implt
{
  ui_message_handlert *message_handler;
  irep_idt function;
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
  if(option == FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT)
  {
    p_impl->function = require_exactly_one_value(option, values);
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
  auto const &function = p_impl->function;
  auto &symbol_table = goto_model.symbol_table;
  auto function_found = symbol_table.lookup(function);
  auto harness_function_found = symbol_table.lookup(harness_function_name);

  if(function_found == nullptr)
  {
    throw invalid_command_line_argument_exceptiont{
      "function that should be harnessed is not found " + id2string(function),
      "--" FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT};
  }

  if(harness_function_found != nullptr)
  {
    throw invalid_command_line_argument_exceptiont{
      "harness function already in the symbol table " +
        id2string(harness_function_name),
      "--" GOTO_HARNESS_GENERATOR_HARNESS_FUNCTION_NAME_OPT};
  }

  auto allocate_objects = allocate_objectst{function_found->mode,
                                            function_found->location,
                                            "__goto_harness",
                                            symbol_table};

  // create body for the function
  code_blockt function_body{};

  const auto &function_type = to_code_type(function_found->type);
  const auto &parameters = function_type.parameters();

  code_function_callt::operandst arguments{};
  arguments.reserve(parameters.size());

  for(const auto &parameter : parameters)
  {
    auto argument = allocate_objects.allocate_automatic_local_object(
      parameter.type(), parameter.get_base_name());
    arguments.push_back(std::move(argument));
  }

  code_function_callt function_call{function_found->symbol_expr(),
                                    std::move(arguments)};
  function_call.add_source_location() = function_found->location;

  function_body.add(std::move(function_call));

  // create the function symbol
  symbolt harness_function_symbol{};
  harness_function_symbol.name = harness_function_symbol.base_name =
    harness_function_symbol.pretty_name = harness_function_name;

  harness_function_symbol.is_lvalue = true;
  harness_function_symbol.mode = function_found->mode;
  harness_function_symbol.type = code_typet{{}, empty_typet{}};
  harness_function_symbol.value = function_body;

  symbol_table.insert(harness_function_symbol);

  goto_model.goto_functions.function_map[harness_function_name].type =
    to_code_type(harness_function_symbol.type);
  auto &body =
    goto_model.goto_functions.function_map[harness_function_name].body;
  goto_convert(
    static_cast<const codet &>(harness_function_symbol.value),
    goto_model.symbol_table,
    body,
    *p_impl->message_handler,
    function_found->mode);
  body.add(goto_programt::make_end_function());
}

void function_call_harness_generatort::validate_options()
{
  if(p_impl->function == ID_empty)
    throw invalid_command_line_argument_exceptiont{
      "required parameter entry function not set",
      "--" FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT};
}
