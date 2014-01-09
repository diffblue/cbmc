/*******************************************************************\

Module: Show Claims

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/xml.h>
#include <util/i2string.h>
#include <util/xml_expr.h>

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
  for(goto_programt::instructionst::const_iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    if(!it->is_assert())
      continue;
      
    const locationt &location=it->location;
      
    const irep_idt &comment=location.get_comment();
    //const irep_idt &function=location.get_function();
    const irep_idt &property_class=location.get_property_class();
    const irep_idt &source=location.get_source();
    const irep_idt description=
      (comment==""?"assertion":comment);
      
    irep_idt property_id=location.get_property_id();
    
    switch(ui)
    {
    case ui_message_handlert::XML_UI:
      {
        xmlt xml_claim("claim");
        xml_claim.new_element("number").data=id2string(property_id); // will go away
        xml_claim.new_element("name").data=id2string(property_id); // will go away
        xml_claim.set_attribute("name", id2string(property_id)); // use this one
        
        xmlt &l=xml_claim.new_element();
        l=xml(it->location);
        
        xml_claim.new_element("description").data=id2string(description);        
        xml_claim.new_element("property").data=id2string(property_class);
        xml_claim.new_element("expression").data=from_expr(ns, identifier, it->guard);
        xml_claim.new_element("source").data=id2string(source);

        std::cout << xml_claim << std::endl;
      }
      break;
      
    case ui_message_handlert::PLAIN:
      std::cout << "Property " << property_id << ":" << std::endl;

      std::cout << "  " << it->location << std::endl
                << "  " << description << std::endl
                << "  " << from_expr(ns, identifier, it->guard) << std::endl;

      if(source!="")
        std::cout << "  in \"" << source << "\"" << std::endl;

      std::cout << std::endl;
      break;

    default:
      assert(false);
    }
  }
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
  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    if(!it->second.is_inlined())
      show_properties(ns, it->first, ui, it->second.body);
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
  show_properties(ns, ui, goto_model.goto_functions);
}

