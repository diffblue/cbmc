/*******************************************************************\

Module: Show Claims

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/xml.h>
#include <util/xml_expr.h>
#include <util/json.h>
#include <util/json_expr.h>
#include <util/i2string.h>

#include <langapi/language_util.h>

#include "show_properties.h"
#include "goto_functions.h"
#include "goto_model.h"

/*******************************************************************\

Function: cbmc_parseoptionst::show_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_properties(
  const namespacet &ns,
  const irep_idt &identifier,
  ui_message_handlert::uit ui,
  const goto_programt &goto_program)
{
  for(const auto & it : goto_program.instructions)
  {
    if(!it.is_assert())
      continue;

    const source_locationt &source_location=it.source_location;

    const irep_idt &comment=source_location.get_comment();
    //const irep_idt &function=location.get_function();
    const irep_idt &property_class=source_location.get_property_class();
    const irep_idt description=
      (comment==""?"assertion":comment);

    irep_idt property_id=source_location.get_property_id();

    switch(ui)
    {
    case ui_message_handlert::XML_UI:
      {
        #if 0
        xmlt xml_claim("claim"); // this will go away, use below
        xml_claim.new_element("number").data=id2string(property_id); // will go away
        xml_claim.new_element("name").data=id2string(property_id); // will go away
        xml_claim.set_attribute("name", id2string(property_id)); // use this one

        xmlt &l=xml_claim.new_element();
        l=xml(it.source_location);

        xml_claim.new_element("description").data=id2string(description);
        xml_claim.new_element("property").data=id2string(property_class);
        xml_claim.new_element("expression").data=from_expr(ns, identifier, it.guard);
        xml_claim.new_element("source").data="";

        std::cout << xml_claim << std::endl;
        #endif

        // use me instead
        xmlt xml_property("property");
        xml_property.set_attribute("name", id2string(property_id)); // use this one
        xml_property.set_attribute("class", id2string(property_class)); // use this one

        xmlt &property_l=xml_property.new_element();
        property_l=xml(it.source_location);

        xml_property.new_element("description").data=id2string(description);
        xml_property.new_element("expression").data=from_expr(ns, identifier, it.guard);

        std::cout << xml_property << std::endl;
      }
      break;

    case ui_message_handlert::JSON_UI:
      assert(false);
      break;

    case ui_message_handlert::PLAIN:
      std::cout << "Property " << property_id << ":" << std::endl;

      std::cout << "  " << it.source_location << std::endl
                << "  " << description << std::endl
                << "  " << from_expr(ns, identifier, it.guard) << std::endl;

      std::cout << std::endl;
      break;

    default:
      assert(false);
    }
  }
}


/*******************************************************************\

Function: cbmc_parseoptionst::show_properties_json

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_properties_json(
  json_arrayt &json_properties,
  const namespacet &ns,
  const irep_idt &identifier,
  const goto_programt &goto_program)
{
  for(const auto & it : goto_program.instructions)
  {
    if(!it.is_assert())
      continue;

    const source_locationt &source_location=it.source_location;

    const irep_idt &comment=source_location.get_comment();
    //const irep_idt &function=location.get_function();
    const irep_idt &property_class=source_location.get_property_class();
    const irep_idt description=
      (comment==""?"assertion":comment);

    irep_idt property_id=source_location.get_property_id();

    json_objectt &json_property=
      json_properties.push_back(jsont()).make_object();
    json_property["name"]=json_stringt(id2string(property_id));
    json_property["class"]=json_stringt(id2string(property_class));
    json_property["sourceLocation"]=json(it.source_location);
    json_property["description"]=json_stringt(id2string(description));
    json_property["expression"]=
      json_stringt(from_expr(ns, identifier, it.guard));
  }
}

/*******************************************************************\

Function: show_properties_json

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_properties_json(
  const namespacet &ns,
  const goto_functionst &goto_functions)
{
  json_arrayt json_properties;

  for(const auto & it : goto_functions.function_map)
  {
    if(!it.second.is_inlined())
      show_properties_json(json_properties, ns, it.first, it.second.body);
  }

  json_objectt json_result;
  json_result["properties"] = json_properties;
  std::cout << ",\n" << json_result;
}

/*******************************************************************\

Function: show_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_properties(
  const namespacet &ns,
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions)
{
  if(ui == ui_message_handlert::JSON_UI)
    show_properties_json(ns, goto_functions);
  else
    for(const auto & it : goto_functions.function_map)
      if(!it.second.is_inlined())
	show_properties(ns, it.first, ui, it.second.body);
}

/*******************************************************************\

Function: show_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_properties(
  const goto_modelt &goto_model,
  ui_message_handlert::uit ui)
{
  const namespacet ns(goto_model.symbol_table);
  if(ui == ui_message_handlert::JSON_UI)
    show_properties_json(ns, goto_model.goto_functions);
  else
    show_properties(ns, ui, goto_model.goto_functions);
}
