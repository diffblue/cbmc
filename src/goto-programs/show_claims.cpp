/*******************************************************************\

Module: Show Claims

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <xml.h>
#include <i2string.h>
#include <xml_expr.h>

#include <langapi/language_util.h>

#include "show_claims.h"
#include "goto_functions.h"

/*******************************************************************\

Function: cbmc_parseoptionst::show_claims

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_claims(
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
    const irep_idt &property=location.get_property();
    const irep_idt description=
      (comment==""?"assertion":comment);
      
    irep_idt claim_name=location.get_claim();
    
    switch(ui)
    {
    case ui_message_handlert::XML_UI:
      {
        xmlt xml_claim("claim");
        xml_claim.new_element("number").data=id2string(claim_name); // will go away
        xml_claim.new_element("name").data=id2string(claim_name);
        
        xmlt &l=xml_claim.new_element();
        l=xml(it->location);
        
        xml_claim.new_element("description").data=id2string(description);        
        xml_claim.new_element("property").data=id2string(property);        
        xml_claim.new_element("expression").data=from_expr(ns, identifier, it->guard);
          
        std::cout << xml_claim << std::endl;
      }
      break;
      
    case ui_message_handlert::PLAIN:
      std::cout << "Claim " << claim_name << ":" << std::endl;

      std::cout << "  " << it->location << std::endl
                << "  " << description << std::endl
                << "  " << from_expr(ns, identifier, it->guard) << std::endl
                << std::endl;
      break;

    default:
      assert(false);
    }
  }
}

/*******************************************************************\

Function: show_claims

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_claims(
  const namespacet &ns,
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions)
{
  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    if(!it->second.is_inlined())
      show_claims(ns, it->first, ui, it->second.body);
}
