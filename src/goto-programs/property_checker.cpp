/*******************************************************************\

Module: Property Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "property_checker.h"

/*******************************************************************\

Function: property_checkert::as_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string property_checkert::as_string(resultt result)
{
  switch(result)
  {
  case property_checkert::PASS: return "OK";
  case property_checkert::FAIL: return "FAILURE";
  case property_checkert::ERROR: return "ERROR";
  case property_checkert::UNKNOWN: return "UNKNOWN";
  }

  return "";
}

/*******************************************************************\

Function: property_checkert::property_checkert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checkert::property_checkert(
  message_handlert &_message_handler):
  messaget(_message_handler)
{
}

/*******************************************************************\

Function: property_checkert::initialize_property_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void property_checkert::initialize_property_map(
  const goto_functionst &goto_functions)
{
  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    if(!it->second.is_inlined() ||
       it->first==goto_functions.entry_point())
    {
      const goto_programt &goto_program=it->second.body;
    
      for(goto_programt::instructionst::const_iterator
          it=goto_program.instructions.begin();
          it!=goto_program.instructions.end();
          it++)
      {
        if(!it->is_assert())
          continue;
      
        const source_locationt &source_location=it->source_location;
      
        irep_idt property_id=source_location.get_property_id();
        
        property_statust &property_status=property_map[property_id];
        property_status.result=UNKNOWN;
        property_status.location=it;
      }
    }
}
