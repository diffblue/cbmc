/*******************************************************************\

Module: Show goto functions

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/xml.h>
#include <util/json.h>
#include <util/json_expr.h>
#include <util/xml_expr.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>

#include <langapi/language_util.h>

#include "show_goto_functions.h"
#include "goto_functions.h"
#include "goto_model.h"

/*******************************************************************\

Function: cbmc_parseoptionst::show_goto_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_goto_functions(
  const namespacet &ns,
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions)
{
  switch(ui)
  {
  case ui_message_handlert::XML_UI:
  {
    //This only prints the list of functions
    xmlt xml_functions("functions");
    forall_goto_functions(it, goto_functions)
    {
      xmlt &xml_function=xml_functions.new_element("function");
      xml_function.set_attribute("name", id2string(it->first));
    }

    std::cout << xml_functions << std::endl;
  }
  break;

  case ui_message_handlert::JSON_UI:
  {
    //This only prints the list of functions
    json_arrayt json_functions;
    forall_goto_functions(it, goto_functions)
    {
      json_objectt &json_function=
        json_functions.push_back(jsont()).make_object();
      json_function["name"]=json_stringt(id2string(it->first));
      json_function["isBodyAvailable"]=
        jsont::json_boolean(it->second.body_available());
      bool is_internal=(has_prefix(id2string(it->first), CPROVER_PREFIX) ||
                        it->first==ID__start);
      json_function["isInternal"]=jsont::json_boolean(is_internal);

      if(it->second.body_available())
      {
        json_arrayt json_instruction_array=json_arrayt();

        for(const goto_programt::instructiont &instruction :
          it->second.body.instructions)
        {
          json_objectt instruction_entry=json_objectt();

          std::ostringstream instruction_id_builder;
          instruction_id_builder << instruction.type;

          instruction_entry["instructionId"]=
            json_stringt(instruction_id_builder.str());

          instruction_entry["sourceLocation"]=
            json(instruction.code.source_location());

          std::ostringstream instruction_builder;
          it->second.body.output_instruction(
            ns, it->first, instruction_builder, instruction);

          instruction_entry["instruction"]=
            json_stringt(instruction_builder.str());


          json_instruction_array.push_back(instruction_entry);
        }

        json_function["instructions"] = json_instruction_array;
      }
    }
    json_objectt json_result;
    json_result["functions"]=json_functions;
    std::cout << ",\n" << json_result;
  }
  break;

  case ui_message_handlert::PLAIN:
    goto_functions.output(ns, std::cout);
    break;
  }
}

/*******************************************************************\

Function: show_goto_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_goto_functions(
  const goto_modelt &goto_model,
  ui_message_handlert::uit ui)
{
  const namespacet ns(goto_model.symbol_table);
  show_goto_functions(ns, ui, goto_model.goto_functions);
}
