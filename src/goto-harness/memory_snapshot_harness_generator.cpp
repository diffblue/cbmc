/******************************************************************\

Module: Harness to initialise memory from memory snapshot

Author: Daniel Poetzl

\******************************************************************/

#include <algorithm>

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

#include <linking/static_lifetime_init.h>

#include "goto_harness_generator_factory.h"
#include "recursive_initialization.h"

void memory_snapshot_harness_generatort::handle_option(
  const std::string &option,
  const std::list<std::string> &values)
{
  if(option == "memory-snapshot")
  {
    memory_snapshot_file = require_exactly_one_value(option, values);
  }
  else if(option == "initial-goto-location")
  {
    initial_goto_location_line = require_exactly_one_value(option, values);
  }
  else if(option == "havoc-variables")
  {
    variables_to_havoc.insert(values.begin(), values.end());
  }
  else if(option == "initial-source-location")
  {
    initial_source_location_line = require_exactly_one_value(option, values);
  }
  else
  {
    throw invalid_command_line_argument_exceptiont(
      "unrecognized option for memory snapshot harness generator",
      "--" + option);
  }
}

void memory_snapshot_harness_generatort::validate_options(
  const goto_modelt &goto_model)
{
  if(memory_snapshot_file.empty())
  {
    throw invalid_command_line_argument_exceptiont(
      "option --memory_snapshot is required",
      "--harness-type initialise-from-memory-snapshot");
  }

  if(entry_function_name.empty())
  {
    INVARIANT(
      !location_number.has_value(),
      "when `function` is empty then the option --initial-location was not "
      "given and thus `location_number` was not set");

    throw invalid_command_line_argument_exceptiont(
      "option --initial-location is required",
      "--harness-type initialise-from-memory-snapshot");
  }

  const auto &goto_functions = goto_model.goto_functions;
  const auto &goto_function =
    goto_functions.function_map.find(entry_function_name);
  if(goto_function == goto_functions.function_map.end())
  {
    throw invalid_command_line_argument_exceptiont(
      "unknown initial location specification", "--initial-location");
  }

  if(!goto_function->second.body_available())
  {
    throw invalid_command_line_argument_exceptiont(
      "given function `" + id2string(entry_function_name) +
        "` does not have a body",
      "--initial-location");
  }

  if(location_number.has_value())
  {
    const auto &goto_program = goto_function->second.body;
    const auto opt_it = goto_program.get_target(*location_number);

    if(!opt_it.has_value())
    {
      throw invalid_command_line_argument_exceptiont(
        "no instruction with location number " +
          std::to_string(*location_number) + " in function " +
          id2string(entry_function_name),
        "--initial-location");
    }
  }

  if(goto_functions.function_map.count(INITIALIZE_FUNCTION) == 0)
  {
    throw invalid_command_line_argument_exceptiont(
      "invalid input program: " + std::string(INITIALIZE_FUNCTION) +
        " not found",
      "<in>");
  }

  const symbol_tablet &symbol_table = goto_model.symbol_table;
  const symbolt *called_function_symbol =
    symbol_table.lookup(entry_function_name);

  if(called_function_symbol == nullptr)
  {
    throw invalid_command_line_argument_exceptiont(
      "function `" + id2string(entry_function_name) +
        "` not found in the symbol table",
      "--initial-location");
  }
}

void memory_snapshot_harness_generatort::add_init_section(
  goto_modelt &goto_model) const
{
  goto_functionst &goto_functions = goto_model.goto_functions;
  symbol_tablet &symbol_table = goto_model.symbol_table;

  goto_functiont &goto_function =
    goto_functions.function_map[entry_function_name];
  const symbolt &function_symbol = symbol_table.lookup_ref(entry_function_name);

  goto_programt &goto_program = goto_function.body;

  // introduce a symbol for a Boolean variable to indicate the point at which
  // the function initialisation is completed
  symbolt &func_init_done_symbol = get_fresh_aux_symbol(
    bool_typet(),
    id2string(entry_function_name),
    "func_init_done",
    function_symbol.location,
    function_symbol.mode,
    symbol_table);
  func_init_done_symbol.is_static_lifetime = true;
  func_init_done_symbol.value = false_exprt();

  const symbol_exprt func_init_done_var = func_init_done_symbol.symbol_expr();

  // initialise func_init_done_var in __CPROVER_initialize if it is present
  // so that it's FALSE value is visible before the harnessed function is called
  goto_programt &cprover_initialize =
    goto_functions.function_map.find(INITIALIZE_FUNCTION)->second.body;
  cprover_initialize.insert_before(
    std::prev(cprover_initialize.instructions.end()),
    goto_programt::make_assignment(
      code_assignt(func_init_done_var, false_exprt())));

  const goto_programt::const_targett start_it =
    goto_program.instructions.begin();

  auto ins_it1 = goto_program.insert_before(
    start_it,
    goto_programt::make_goto(goto_program.const_cast_target(start_it)));
  ins_it1->guard = func_init_done_var;

  auto ins_it2 = goto_program.insert_after(
    ins_it1,
    goto_programt::make_assignment(
      code_assignt(func_init_done_var, true_exprt())));

  goto_program.compute_location_numbers();
  goto_program.insert_after(
    ins_it2,
    goto_programt::make_goto(goto_program.const_cast_target(
      location_number.has_value() ? *goto_program.get_target(*location_number)
                                  : start_it)));
}

code_blockt memory_snapshot_harness_generatort::add_assignments_to_globals(
  const symbol_tablet &snapshot,
  goto_modelt &goto_model) const
{
  recursive_initializationt recursive_initialization{
    recursive_initialization_configt{}, goto_model};

  code_blockt code;
  for(const auto &pair : snapshot)
  {
    const symbolt &symbol = pair.second;
    if(!symbol.is_static_lifetime)
      continue;

    if(variables_to_havoc.count(symbol.base_name) == 0)
    {
      code.add(code_assignt{symbol.symbol_expr(), symbol.value});
    }
    else
    {
      recursive_initialization.initialize(symbol.symbol_expr(), 0, {}, code);
    }
  }
  return code;
}

void memory_snapshot_harness_generatort::add_call_with_nondet_arguments(
  const symbolt &called_function_symbol,
  code_blockt &code) const
{
  const code_typet &code_type = to_code_type(called_function_symbol.type);

  code_function_callt::argumentst arguments;

  for(const code_typet::parametert &parameter : code_type.parameters())
  {
    arguments.push_back(side_effect_expr_nondett{
      parameter.type(), called_function_symbol.location});
  }

  code.add(code_function_callt{called_function_symbol.symbol_expr(),
                               std::move(arguments)});
}

void memory_snapshot_harness_generatort::
  insert_harness_function_into_goto_model(
    goto_modelt &goto_model,
    const symbolt &function) const
{
  const auto r = goto_model.symbol_table.insert(function);
  CHECK_RETURN(r.second);

  auto function_iterator_pair = goto_model.goto_functions.function_map.emplace(
    function.name, goto_functiont{});

  CHECK_RETURN(function_iterator_pair.second);

  goto_functiont &harness_function = function_iterator_pair.first->second;
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

  const bool r = parse_json(memory_snapshot_file, message_handler, json);

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
    // throws a deserialization_exceptiont or an
    // incorrect_goto_program_exceptiont
    // on failure to read JSON symbol table
    symbol_table_from_json(json, snapshot);
  }
}

void memory_snapshot_harness_generatort::generate(
  goto_modelt &goto_model,
  const irep_idt &harness_function_name)
{
  symbol_tablet snapshot;
  get_memory_snapshot(memory_snapshot_file, snapshot);

  symbol_tablet &symbol_table = goto_model.symbol_table;
  goto_functionst &goto_functions = goto_model.goto_functions;

  const symbolt *called_function_symbol =
    symbol_table.lookup(entry_function_name);

  add_init_section(goto_model);

  code_blockt harness_function_body =
    add_assignments_to_globals(snapshot, goto_model);

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
  insert_harness_function_into_goto_model(goto_model, harness_function_symbol);

  goto_functions.update();
}

memory_snapshot_harness_generatort::entry_goto_locationt
memory_snapshot_harness_generatort::parse_goto_location(
  const std::string &cmdl_option)
{
  std::vector<std::string> start;
  split_string(cmdl_option, ':', start, true);

  if(
    start.empty() || start.front().empty() ||
    (start.size() == 2 && start.back().empty()) || start.size() > 2)
  {
    throw invalid_command_line_argument_exceptiont(
      "invalid initial location specification", "--initial-location");
  }

  if(start.size() == 2)
  {
    const auto location_number = string2optional_unsigned(start.back());
    CHECK_RETURN(location_number.has_value());
    return entry_goto_locationt{start.front(), *location_number};
  }
  else
  {
    return entry_goto_locationt{start.front()};
  }
}

memory_snapshot_harness_generatort::entry_source_locationt
memory_snapshot_harness_generatort::parse_source_location(
  const std::string &cmdl_option)
{
  std::string initial_file_string;
  std::string initial_line_string;
  split_string(
    cmdl_option, ':', initial_file_string, initial_line_string, true);

  if(initial_file_string.empty() || initial_line_string.empty())
  {
    throw invalid_command_line_argument_exceptiont(
      "invalid initial location specification", "--initial-file-line");
  }

  const auto line_number = string2optional_unsigned(initial_line_string);
  CHECK_RETURN(line_number.has_value());
  return entry_source_locationt{initial_file_string, *line_number};
}

memory_snapshot_harness_generatort::entry_locationt
memory_snapshot_harness_generatort::initialize_entry_via_goto(
  const entry_goto_locationt &entry_goto_location,
  const goto_functionst &goto_functions)
{
  PRECONDITION(!entry_goto_location.function_name.empty());
  const irep_idt &function_name = entry_goto_location.function_name;

  // by function(+location): search for the function then jump to n-th
  // location, then check the number
  const auto &goto_function =
    goto_functions.function_map.find(entry_goto_location.function_name);
  if(
    goto_function != goto_functions.function_map.end() &&
    goto_function->second.body_available())
  {
    const auto &goto_program = goto_function->second.body;

    const auto corresponding_instruction =
      entry_goto_location.find_first_corresponding_instruction(
        goto_program.instructions);

    if(corresponding_instruction != goto_program.instructions.end())
      return entry_locationt{function_name, corresponding_instruction};
  }
  throw invalid_command_line_argument_exceptiont(
    "could not find the specified entry point", "--initial-goto-location");
}

memory_snapshot_harness_generatort::entry_locationt
memory_snapshot_harness_generatort::initialize_entry_via_source(
  const entry_source_locationt &entry_source_location,
  const goto_functionst &goto_functions)
{
  PRECONDITION(!entry_source_location.file_name.empty());

  // by line: iterate over all instructions until source location match
  for(const auto &entry : goto_functions.function_map)
  {
    const auto &goto_function = entry.second;
    // if !body_available() then body.instruction.empty() and that's fine
    const auto &goto_program = goto_function.body;

    const auto corresponding_instruction =
      entry_source_location.find_first_corresponding_instruction(
        goto_program.instructions);

    if(corresponding_instruction != goto_program.instructions.end())
      return entry_locationt{entry.first, corresponding_instruction};
  }
  throw invalid_command_line_argument_exceptiont(
    "could not find the specified entry point", "--initial-source-location");
}

goto_programt::const_targett memory_snapshot_harness_generatort::
  entry_goto_locationt::find_first_corresponding_instruction(
    const goto_programt::instructionst &instructions) const
{
  if(!location_number.has_value())
    return instructions.begin();

  return std::find_if(
    instructions.begin(),
    instructions.end(),
    [this](const goto_programt::instructiont &instruction) {
      return *location_number == instruction.location_number;
    });
}

goto_programt::const_targett memory_snapshot_harness_generatort::
  entry_source_locationt::find_first_corresponding_instruction(
    const goto_programt::instructionst &instructions) const
{
  return std::find_if(
    instructions.begin(),
    instructions.end(),
    [this](const goto_programt::instructiont &instruction) {
      return instruction.source_location.get_file() == file_name &&
             safe_string2unsigned(id2string(
               instruction.source_location.get_line())) >= line_number;
    });
}
