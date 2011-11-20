/*******************************************************************\

Module: Show Claims

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <xml.h>
#include <i2string.h>
#include <xml_irep.h>

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
  const goto_programt &goto_program,
  std::map<irep_idt, unsigned> &claim_counter)
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
    const irep_idt &function=location.get_function();
    const irep_idt &property=location.get_property();
    const irep_idt description=
      (comment==""?"assertion":comment);
      
    unsigned priority=location.get_priority();
      
    unsigned &count=claim_counter[function];
    
    count++;

    std::string claim_name=
      function==""?i2string(count):
      id2string(function)+"."+i2string(count);
    
    switch(ui)
    {
    case ui_message_handlert::XML_UI:
      {
        xmlt xml("claim");
        xml.new_element("number").data=claim_name;
        xml.new_element("name").data=claim_name;
        
        xmlt &l=xml.new_element();
        convert(it->location, l);
        l.name="location";
        
        l.new_element("line").data=id2string(location.get_line());
        l.new_element("file").data=id2string(location.get_file());
        l.new_element("function").data=id2string(location.get_function());
        
        xml.new_element("description").data=id2string(description);        
        xml.new_element("property").data=id2string(property);        
        xml.new_element("expression").data=from_expr(ns, identifier, it->guard);
        xml.new_element("priority").data=i2string(priority);
          
        std::cout << xml << std::endl;
      }
      break;
      
    case ui_message_handlert::PLAIN:
      std::cout << "Claim " << claim_name << ":" << std::endl;

      std::cout << "  " << it->location << std::endl
                << "  " << description << std::endl
                << "  " << from_expr(ns, identifier, it->guard) << std::endl
                << "  priority " << priority << std::endl
                << std::endl;
      break;

    default:
      assert(false);
    }
  }
}

/*******************************************************************\

Function: cbmc_parseoptionst::show_claims

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_claims(
  const namespacet &ns,
  ui_message_handlert::uit ui,
  const goto_programt &goto_program)
{
  std::map<irep_idt, unsigned> count;
  show_claims(ns, "", ui, goto_program, count);
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
  std::map<irep_idt, unsigned> count;

  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    if(!it->second.is_inlined())
      show_claims(ns, it->first, ui, it->second.body, count);
}
