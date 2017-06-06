/*******************************************************************\

Module: Property Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Property Checker Interface

#include "property_checker.h"

std::string property_checkert::as_string(resultt result)
{
  switch(result)
  {
  case property_checkert::resultt::PASS: return "OK";
  case property_checkert::resultt::FAIL: return "FAILURE";
  case property_checkert::resultt::ERROR: return "ERROR";
  case property_checkert::resultt::UNKNOWN: return "UNKNOWN";
  }

  return "";
}

property_checkert::property_checkert(
  message_handlert &_message_handler):
  messaget(_message_handler)
{
}

void property_checkert::initialize_property_map(
  const goto_functionst &goto_functions)
{
  forall_goto_functions(it, goto_functions)
    if(!it->second.is_inlined() ||
       it->first==goto_functions.entry_point())
    {
      const goto_programt &goto_program=it->second.body;

      forall_goto_program_instructions(i_it, goto_program)
      {
        if(!i_it->is_assert())
          continue;

        const source_locationt &source_location=i_it->source_location;

        irep_idt property_id=source_location.get_property_id();

        property_statust &property_status=property_map[property_id];
        property_status.result=resultt::UNKNOWN;
        property_status.location=i_it;
      }
    }
}
