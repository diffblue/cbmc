/******************************************************************\

Module: Harness to initialise memory from memory snapshot

Author: Daniel Poetzl

\******************************************************************/

#include "memory_snapshot_harness_generator.h"

#include <goto-programs/goto_convert.h>

#include <json/json_parser.h>

#include <json-symtab-language/json_symbol_table.h>

#include <util/exception_utils.h>
#include <util/fresh_symbol.h>
#include <util/message.h>
#include <util/string2int.h>
#include <util/string_utils.h>
#include <util/symbol_table.h>

#include "goto_harness_generator_factory.h"

void memory_snapshot_harness_generatort::handle_option(
  const std::string &option,
  const std::list<std::string> &values)
{
  if(option == "memory-snapshot")
  {
    memory_snapshot = require_exactly_one_value(option, values);
  }
  else if(option == "initial-location")
  {
    const std::string initial_location =
      require_exactly_one_value(option, values);

    std::vector<std::string> start;
    split_string(initial_location, ':', start, true);

    if(
      start.size() == 0 || (start.size() >= 1 && start.front().empty()) ||
      (start.size() == 2 && start.back().empty()) || start.size() > 2)
    {
      throw invalid_command_line_argument_exceptiont(
        "invalid initial location specification", "--initial-location");
    }

    function = start.front();

    if(start.size() == 2)
    {
      location_number = optionalt<unsigned>(safe_string2unsigned(start.back()));
    }
  }
  else
  {
    throw invalid_command_line_argument_exceptiont(
      "unrecognized option for memory snapshot harness generator",
      "--" + option);
  }
}

void memory_snapshot_harness_generatort::validate_options()
{
  if(memory_snapshot.empty())
  {
    throw invalid_command_line_argument_exceptiont(
      "option --memory_snapshot is required",
      "--harness-type initialise-from-memory-snapshot");
  }

  if(function.empty())
  {
    INVARIANT(
      location_number.has_value(),
      "when `function` is empty then the option --initial-location was not "
      "given and thus `location_number` was not set");

    throw invalid_command_line_argument_exceptiont(
      "option --initial-location is required",
      "--harness-type initialise-from-memory-snapshot");
  }
}

void memory_snapshot_harness_generatort::add_init_section(
  goto_modelt &goto_model) const
{
  goto_functionst &goto_functions = goto_model.goto_functions;
  symbol_tablet &symbol_table = goto_model.symbol_table;

  goto_functiont &goto_function = goto_functions.function_map[function];
  const symbolt &function_symbol = symbol_table.lookup_ref(function);

  goto_programt &goto_program = goto_function.body;

  const symbolt &symbol = get_fresh_aux_symbol(
    bool_typet(),
    id2string(function),
    "func_init_done",
    source_locationt(),
    function_symbol.mode,
    symbol_table);

  const symbol_exprt &var = symbol.symbol_expr();

  // initialise var in __CPROVER_initialize if it is present
  const auto f_it =
    goto_functions.function_map.find(CPROVER_PREFIX "initialize");

  if(f_it != goto_functions.function_map.end())
  {
    goto_programt &goto_program = f_it->second.body;

    auto init_it =
      goto_program.insert_before(std::prev(goto_program.instructions.end()));

    init_it->make_assignment(code_assignt(var, false_exprt()));
  }

  const goto_programt::const_targett start_it =
    goto_program.instructions.begin();

  goto_programt::const_targett it;

  if(location_number.has_value())
  {
    const auto opt_it = goto_program.get_target(*location_number);

    if(!opt_it.has_value())
    {
      throw invalid_command_line_argument_exceptiont(
        "no instruction with location number " +
          std::to_string(*location_number) + " in function " +
          id2string(function),
        "--initial-location");
    }

    it = *opt_it;
  }
  else
  {
    it = start_it;
  }

  auto ins_it1 = goto_program.insert_before(start_it);
  ins_it1->make_goto(goto_program.const_cast_target(start_it));
  ins_it1->guard = var;

  auto ins_it2 = goto_program.insert_after(ins_it1);
  ins_it2->make_assignment(code_assignt(var, true_exprt()));

  auto ins_it3 = goto_program.insert_after(ins_it2);
  ins_it3->make_goto(goto_program.const_cast_target(it));
}

void memory_snapshot_harness_generatort::add_assignments_to_globals(
  const symbol_tablet &snapshot,
  code_blockt &code) const
{
  for(const auto &pair : snapshot)
  {
    const symbolt &symbol = pair.second;

    if(!symbol.is_static_lifetime)
      continue;

    code_assignt code_assign(symbol.symbol_expr(), symbol.value);

    code.add(code_assign);
  }
}

void memory_snapshot_harness_generatort::add_call_with_nondet_arguments(
  const symbolt &called_function_symbol,
  code_blockt &code) const
{
  const code_typet &code_type = to_code_type(called_function_symbol.type);

  code_function_callt::argumentst arguments;

  for(const code_typet::parametert &parameter : code_type.parameters())
  {
    arguments.push_back(side_effect_expr_nondett(parameter.type()));
  }

  code_function_callt function_call(
    called_function_symbol.symbol_expr(), arguments);
  code.add(function_call);
}

void memory_snapshot_harness_generatort::insert_function(
  goto_modelt &goto_model,
  const symbolt &function) const
{
  const auto r = goto_model.symbol_table.insert(function);
  CHECK_RETURN(r.second);

  auto f_it = goto_model.goto_functions.function_map.insert(
    std::make_pair(function.name, goto_functiont()));
  CHECK_RETURN(f_it.second);

  goto_functiont &harness_function = f_it.first->second;
  harness_function.type = to_code_type(function.type);

  goto_convert(
    to_code_block(to_code(function.value)),
    goto_model.symbol_table,
    harness_function.body,
    message_handler,
    function.mode);

  harness_function.body.add(goto_programt::make_end_function());
}

void memory_snapshot_harness_generatort::get_memory_snapshot(
  const std::string &file,
  symbol_tablet &snapshot) const
{
  jsont json;

  const bool r = parse_json(memory_snapshot, message_handler, json);

  if(r)
  {
    throw deserialization_exceptiont("failed to read JSON memory snapshot");
  }

  if(json.is_array())
  {
    // since memory-analyzer produces an array JSON we need to search it
    // to find the first JSON object that is a symbol table
    const auto &jarr = to_json_array(json);
    for(auto const &arr_element : jarr)
    {
      if(!arr_element.is_object())
        continue;
      const auto &json_obj = to_json_object(arr_element);
      const auto it = json_obj.find("symbolTable");
      if(it != json_obj.end())
      {
        symbol_table_from_json(json_obj, snapshot);
        return;
      }
    }
    throw deserialization_exceptiont(
      "JSON memory snapshot does not contain symbol table");
  }
  else
  {
    // throws a deserialization_exceptiont or an incorrect_goto_program_exceptiont
    // on failure to read JSON symbol table
    symbol_table_from_json(json, snapshot);
  }
}

void memory_snapshot_harness_generatort::generate(
  goto_modelt &goto_model,
  const irep_idt &harness_function_name)
{
  symbol_tablet snapshot;
  get_memory_snapshot(memory_snapshot, snapshot);

  symbol_tablet &symbol_table = goto_model.symbol_table;
  goto_functionst &goto_functions = goto_model.goto_functions;

  const symbolt *called_function_symbol = symbol_table.lookup(function);

  if(called_function_symbol == nullptr)
  {
    throw invalid_command_line_argument_exceptiont(
      "function `" + id2string(function) + "` not found in the symbol table",
      "--initial-location");
  }

  {
    const auto f_it = goto_functions.function_map.find(function);

    if(f_it == goto_functions.function_map.end())
    {
      throw invalid_command_line_argument_exceptiont(
        "goto function `" + id2string(function) + "` not found",
        "--initial-location");
    }

    if(!f_it->second.body_available())
    {
      throw invalid_command_line_argument_exceptiont(
        "given function `" + id2string(function) + "` does not have a body",
        "--initial-location");
    }
  }

  add_init_section(goto_model);

  if(symbol_table.has_symbol(harness_function_name))
  {
    throw invalid_command_line_argument_exceptiont(
      "harness function `" + id2string(harness_function_name) +
        "` already in "
        "the symbol table",
      "--" GOTO_HARNESS_GENERATOR_HARNESS_FUNCTION_NAME_OPT);
  }

  code_blockt harness_function_body;

  add_assignments_to_globals(snapshot, harness_function_body);

  add_call_with_nondet_arguments(
    *called_function_symbol, harness_function_body);

  // Create harness function symbol

  symbolt harness_function_symbol;
  harness_function_symbol.name = harness_function_name;
  harness_function_symbol.base_name = harness_function_name;
  harness_function_symbol.pretty_name = harness_function_name;

  harness_function_symbol.is_lvalue = true;
  harness_function_symbol.mode = called_function_symbol->mode;
  harness_function_symbol.type = code_typet({}, empty_typet());
  harness_function_symbol.value = harness_function_body;

  // Add harness function to goto model and symbol table
  insert_function(goto_model, harness_function_symbol);

  goto_functions.update();
}
