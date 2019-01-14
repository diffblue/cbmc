/*******************************************************************\

Module: Goto Program

Author: Thomas Kiley

\*******************************************************************/

/// \file
/// Goto Program

#include "show_goto_functions_json.h"

#include <iostream>
#include <sstream>

#include <util/json_irep.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>

#include <langapi/language_util.h>

#include "goto_functions.h"
#include "goto_model.h"

/// For outputting the GOTO program in a readable JSON format.
/// \param _ns: the namespace to use to resolve names with
/// \param _list_only: output only list of functions, but not their bodies
show_goto_functions_jsont::show_goto_functions_jsont(
  const namespacet &_ns,
  bool _list_only)
  : ns(_ns), list_only(_list_only)
{}

/// Walks through all of the functions in the program and returns a JSON object
/// representing all their functions
/// \param goto_functions: the goto functions that make up the program
json_objectt show_goto_functions_jsont::convert(
  const goto_functionst &goto_functions)
{
  json_arrayt json_functions;
  const json_irept no_comments_irep_converter(false);

  const auto sorted = goto_functions.sorted();

  for(const auto &function_entry : sorted)
  {
    const irep_idt &function_name = function_entry->first;
    const goto_functionst::goto_functiont &function = function_entry->second;

    json_objectt &json_function=
      json_functions.push_back(jsont()).make_object();
    json_function["name"] = json_stringt(function_name);
    json_function["isBodyAvailable"]=
      jsont::json_boolean(function.body_available());
    bool is_internal=
      has_prefix(id2string(function_name), CPROVER_PREFIX) ||
      has_prefix(id2string(function_name), "java::array[") ||
      has_prefix(id2string(function_name), "java::org.cprover") ||
      has_prefix(id2string(function_name), "java::java");
    json_function["isInternal"]=jsont::json_boolean(is_internal);

    if(list_only)
      continue;

    if(function.body_available())
    {
      json_arrayt json_instruction_array=json_arrayt();

      for(const goto_programt::instructiont &instruction :
        function.body.instructions)
      {
        json_stringt instruction_id(instruction.to_string());
        json_objectt instruction_entry(
          {{"instructionId", std::move(instruction_id)}});

        if(instruction.code.source_location().is_not_nil())
        {
          instruction_entry["sourceLocation"]=
            json(instruction.code.source_location());
        }

        std::ostringstream instruction_builder;
        function.body.output_instruction(
          ns, function_name, instruction_builder, instruction);

        instruction_entry["instruction"]=
          json_stringt(instruction_builder.str());

        if(!instruction.code.operands().empty())
        {
          json_arrayt operand_array;
          for(const exprt &operand : instruction.code.operands())
          {
            json_objectt operand_object=
              no_comments_irep_converter.convert_from_irep(
                operand);
            operand_array.push_back(operand_object);
          }
          instruction_entry["operands"] = std::move(operand_array);
        }

        if(!instruction.guard.is_true())
        {
          json_objectt guard_object=
            no_comments_irep_converter.convert_from_irep(
              instruction.guard);

          instruction_entry["guard"] = std::move(guard_object);
        }

        json_instruction_array.push_back(std::move(instruction_entry));
      }

      json_function["instructions"] = std::move(json_instruction_array);
    }
  }

  return json_objectt({{"functions", json_functions}});
}

/// Print the json object generated by
/// show_goto_functions_jsont::show_goto_functions to the provided stream (e.g.
/// std::cout)
/// \param goto_functions: the goto functions that make up the program
/// \param out: the stream to write the object to
/// \param append: should a command and newline be appended to the stream before
///   writing the JSON object. Defaults to true
void show_goto_functions_jsont::operator()(
  const goto_functionst &goto_functions,
  std::ostream &out,
  bool append)
{
  if(append)
  {
    out << ",\n";
  }
  out << convert(goto_functions);
}
