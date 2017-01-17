/*******************************************************************\

Module: Goto Program

Author: Thomas Kiley

\*******************************************************************/

#include <iostream>
#include <sstream>

#include <util/json.h>
#include <util/json_expr.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>

#include <langapi/language_util.h>

#include "goto_functions.h"
#include "goto_model.h"
#include "show_goto_functions_json.h"

/*******************************************************************\

Function: show_goto_functions_jsont::show_goto_functions_jsont

  Inputs:
   ns - the namespace to use to resolve names with

 Outputs:

 Purpose: For outputing the GOTO program in a readable JSON format.

\*******************************************************************/

show_goto_functions_jsont::show_goto_functions_jsont(const namespacet &ns):
  ns(ns)
{}

/*******************************************************************\

Function: show_goto_functions_jsont::show_goto_functions

  Inputs:
   goto_functions - the goto functions that make up the program

 Outputs:

 Purpose: Walks through all of the functions in the program and outputs
          JSON

\*******************************************************************/

void show_goto_functions_jsont::show_goto_functions(
  const goto_functionst &goto_functions)
{
  json_arrayt json_functions;
  for(const auto &function_entry : goto_functions.function_map)
  {
    const irep_idt &function_name=function_entry.first;
    const goto_functionst::goto_functiont &function=function_entry.second;

    json_objectt &json_function=
      json_functions.push_back(jsont()).make_object();
    json_function["name"]=json_stringt(id2string(function_name));
    json_function["isBodyAvailable"]=
      jsont::json_boolean(function.body_available());
    bool is_internal=(has_prefix(id2string(function_name), CPROVER_PREFIX) ||
                      function_name==ID__start);
    json_function["isInternal"]=jsont::json_boolean(is_internal);

    if(function.body_available())
    {
      json_arrayt json_instruction_array=json_arrayt();

      for(const goto_programt::instructiont &instruction :
        function.body.instructions)
      {
        json_objectt instruction_entry=json_objectt();

        std::ostringstream instruction_id_builder;
        instruction_id_builder << instruction.type;

        instruction_entry["instructionId"]=
          json_stringt(instruction_id_builder.str());

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

        json_instruction_array.push_back(instruction_entry);
      }

      json_function["instructions"]=json_instruction_array;
    }
  }
  json_objectt json_result;
  json_result["functions"]=json_functions;

  // Should this actually be through a message handler
  std::cout << ",\n" << json_result;
}
