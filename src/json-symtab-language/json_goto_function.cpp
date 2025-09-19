/*******************************************************************\

Module: JSON goto_function deserialization

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// JSON goto_function deserialization

#include "json_goto_function.h"

#include <util/exception_utils.h>
#include <util/expr.h>
#include <util/json_irep.h>
#include <util/string2int.h>

#include "json_symbol.h"

/// Return code at "code" key in a JSON object, if any.
/// \param json: The json object to pick the value from.
/// \return An expression, unless an exception was thrown before.
static goto_instruction_codet try_get_code(const json_objectt &json)
{
  auto code_it = json.find("code");
  if(code_it == json.end())
    throw deserialization_exceptiont{
      "instruction_from_json: key 'code' not found"};

  json_irept json2irep{true};
  irept code_irep = json2irep.convert_from_json(code_it->second);
  return static_cast<goto_instruction_codet &>(code_irep);
}

/// Return code at "code" key in a JSON object, if any.
/// \param json: The json object to pick the value from.
/// \param code_id: The expected code type
/// \return An expression, unless an exception was thrown before.
static goto_instruction_codet
try_get_code(const json_objectt &json, const irep_idt &code_id)
{
  goto_instruction_codet code = try_get_code(json);
  if(code.get_statement() != code_id)
  {
    throw deserialization_exceptiont{
      "instruction_from_json: expected '" + id2string(code_id) + "', got '" +
      id2string(code.get_statement()) + "'"};
  }
  return code;
}

/// Return expression at "guard" key in a JSON object, if any.
/// \param json: The json object to pick the value from.
/// \return An expression, unless an exception was thrown before.
static exprt try_get_guard(const json_objectt &json)
{
  auto guard_it = json.find("guard");
  if(guard_it == json.end())
    throw deserialization_exceptiont{
      "instruction_from_json: key 'guard' not found"};

  json_irept json2irep{true};
  irept guard_irep = json2irep.convert_from_json(guard_it->second);
  return static_cast<exprt &>(guard_irep);
}

/// Deserialize a goto_programt::instructiont from JSON
/// \param json: The JSON object representing an instruction
/// \return A goto_programt::instructiont
static goto_programt::instructiont
instruction_from_json(const json_objectt &json)
{
  auto id_it = json.find("instructionId");
  if(id_it == json.end())
  {
    throw deserialization_exceptiont{
      "instruction_from_json: key 'instructionId' not found"};
  }
  auto instruction_type = try_get_string(id_it->second, "instructionId");

  source_locationt source_location = source_locationt::nil();
  auto location_it = json.find("sourceLocation");
  if(location_it != json.end())
    source_location = try_get_source_location(location_it->second);

  if(instruction_type == "GOTO")
  {
    return goto_programt::make_incomplete_goto(
      try_get_guard(json), source_location);
  }
  else if(instruction_type == "ASSUME")
  {
    return goto_programt::make_assumption(try_get_guard(json), source_location);
  }
  else if(instruction_type == "ASSERT")
  {
    return goto_programt::make_assertion(try_get_guard(json), source_location);
  }
  else if(instruction_type == "OTHER")
  {
    return goto_programt::make_other(try_get_code(json), source_location);
  }
  else if(instruction_type == "SKIP")
  {
    return goto_programt::make_skip(source_location);
  }
  else if(instruction_type == "START_THREAD")
  {
    return goto_programt::instructiont{
      static_cast<const goto_instruction_codet &>(get_nil_irep()),
      source_location,
      START_THREAD,
      nil_exprt{},
      {}};
  }
  else if(instruction_type == "END_THREAD")
  {
    return goto_programt::instructiont{
      static_cast<const goto_instruction_codet &>(get_nil_irep()),
      source_location,
      END_THREAD,
      nil_exprt{},
      {}};
  }
  else if(instruction_type == "LOCATION")
  {
    return goto_programt::make_location(source_location);
  }
  else if(instruction_type == "END_FUNCTION")
  {
    return goto_programt::make_end_function(source_location);
  }
  else if(instruction_type == "ATOMIC_BEGIN")
  {
    return goto_programt::make_atomic_begin(source_location);
  }
  else if(instruction_type == "ATOMIC_END")
  {
    return goto_programt::make_atomic_end(source_location);
  }
  else if(instruction_type == "SET_RETURN_VALUE")
  {
    return goto_programt::make_set_return_value(
      to_code_return(try_get_code(json, ID_return)).return_value(),
      source_location);
  }
  else if(instruction_type == "ASSIGN")
  {
    return goto_programt::make_assignment(
      to_code_assign(try_get_code(json, ID_assign)), source_location);
  }
  else if(instruction_type == "DECL")
  {
    return goto_programt::make_decl(
      to_code_decl(try_get_code(json, ID_decl)), source_location);
  }
  else if(instruction_type == "DEAD")
  {
    return goto_programt::instructiont{
      to_code_dead(try_get_code(json, ID_dead)),
      source_location,
      DEAD,
      nil_exprt{},
      {}};
  }
  else if(instruction_type == "FUNCTION_CALL")
  {
    return goto_programt::make_function_call(
      to_code_function_call(try_get_code(json, ID_function_call)),
      source_location);
  }
  else if(instruction_type == "THROW")
  {
    return goto_programt::make_throw(source_location);
  }
  else if(instruction_type == "CATCH")
  {
    return goto_programt::make_catch(source_location);
  }
  else
  {
    throw deserialization_exceptiont{
      "instruction_from_json: got unexpected instructionId '" +
      instruction_type + "'"};
  }
}

/// Deserialize a goto_programt from JSON
/// \param json: The JSON object representing a goto_program
/// \return A goto_programt
static goto_programt goto_program_from_json(const jsont &json)
{
  if(!json.is_array())
    throw deserialization_exceptiont{"goto_program_from_json takes an array"};

  goto_programt program;

  // First pass: create all instructions
  std::map<unsigned, goto_programt::targett> target_map;
  for(const auto &instruction_json : to_json_array(json))
  {
    if(!instruction_json.is_object())
      throw deserialization_exceptiont{"instruction_from_json takes an object"};

    const json_objectt &json_object = to_json_object(instruction_json);
    auto location_number_it = json_object.find("locationNumber");
    std::optional<unsigned> loc_unsigned;
    if(
      location_number_it != json_object.end() &&
      location_number_it->second.is_number())
    {
      loc_unsigned = string2optional_unsigned(location_number_it->second.value);
    }
    if(!loc_unsigned.has_value())
    {
      throw deserialization_exceptiont{
        "goto_program_from_json: key 'locationNumber' not found or does not "
        "map to an unsigned number"};
    }

    program.add(instruction_from_json(json_object));
    auto new_key =
      target_map.insert({*loc_unsigned, std::prev(program.instructions.end())})
        .second;
    if(!new_key)
    {
      throw deserialization_exceptiont{
        "goto_program_from_json: duplicate locationNumber " +
        location_number_it->second.value};
    }
  }

  // Second pass: resolve targets
  goto_programt::targett instruction_it = program.instructions.begin();
  for(const auto &instruction_json : to_json_array(json))
  {
    for(const auto &kv : to_json_object(instruction_json))
    {
      if(
        kv.first == "code" || kv.first == "guard" ||
        kv.first == "instruction" || kv.first == "instructionId" ||
        kv.first == "locationNumber" || kv.first == "sourceLocation")
      {
        continue;
      }
      else if(kv.first == "labels")
      {
        if(!kv.second.is_array())
          throw deserialization_exceptiont{"labels must be an array"};

        for(const auto &label : to_json_array(kv.second))
        {
          if(!label.is_string())
            throw deserialization_exceptiont{"label must be a string"};
          instruction_it->labels.push_back(label.value);
        }
      }
      else if(kv.first == "targets")
      {
        if(!kv.second.is_array())
          throw deserialization_exceptiont{"targets must be an array"};

        for(const auto &target : to_json_array(kv.second))
        {
          std::optional<unsigned> target_unsigned =
            string2optional_unsigned(target.value);
          if(!target.is_number() || !target_unsigned.has_value())
            throw deserialization_exceptiont{
              "target must be an unsigned number"};
          auto target_it = target_map.find(*target_unsigned);
          if(target_it == target_map.end())
            throw deserialization_exceptiont{"target not in function"};
          instruction_it->targets.push_back(target_it->second);
        }

        if(
          !instruction_it->is_incomplete_goto() ||
          instruction_it->targets.empty())
        {
          throw deserialization_exceptiont{
            "goto_program_from_json: invalid targets entry"};
        }
        goto_programt::targett target = instruction_it->targets.back();
        instruction_it->targets.pop_back();
        instruction_it->complete_goto(target);
      }
      else
      {
        throw deserialization_exceptiont{
          "goto_program_from_json: unexpected key '" + kv.first + "'"};
      }
    }

    ++instruction_it;
  }

  return program;
}

goto_functiont goto_function_from_json(const json_objectt &json)
{
  goto_functiont result;

  for(const auto &kv : json)
  {
    if(kv.first == "instructions")
    {
      result.body = goto_program_from_json(kv.second);
    }
    else if(kv.first == "parameterIdentifiers")
    {
      if(!kv.second.is_array())
      {
        throw deserialization_exceptiont{
          "parameterIdentifiers must be an array"};
      }

      for(const auto &param : to_json_array(kv.second))
      {
        if(!param.is_string())
        {
          throw deserialization_exceptiont{
            "parameter identifier must be a string"};
        }
        result.parameter_identifiers.push_back(param.value);
      }
    }
    else if(kv.first == "isHidden")
    {
      if(try_get_bool(kv.second, "isHidden"))
        result.make_hidden();
    }
    else if(kv.first == "name")
    {
      // ignored, already processed by goto_functions_from_json
    }
    else if(kv.first == "isBodyAvailable" || kv.first == "isInternal")
    {
      // ignored, computed at runtime
    }
    else
    {
      throw deserialization_exceptiont{
        "goto_function_from_json: unexpected key '" + kv.first + "'"};
    }
  }

  return result;
}
