/*******************************************************************\

Module: Set Claims

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/i2string.h>
#include <util/hash_cont.h>

#include "set_properties.h"

/*******************************************************************\

Function: set_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void set_properties(
  goto_programt &goto_program,
  hash_set_cont<irep_idt, irep_id_hash> &property_set)
{
  for(goto_programt::instructionst::iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    if(!it->is_assert()) continue;
    
    irep_idt property_id=it->location.get_property_id();

    hash_set_cont<irep_idt, irep_id_hash>::iterator
      c_it=property_set.find(property_id);
      
    if(c_it==property_set.end())
      it->type=SKIP;
    else
      property_set.erase(c_it);
  }
}

/*******************************************************************\

Function: label_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void label_properties(
  goto_programt &goto_program,
  std::map<irep_idt, unsigned> &property_counters)
{
  for(goto_programt::instructionst::iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    if(!it->is_assert()) continue;
    
    irep_idt function=it->location.get_function();
    unsigned &count=property_counters[function];
    
    count++;
    
    std::string property_id=
      function==""?i2string(count):
      id2string(function)+"."+i2string(count);
    
    it->location.set_property_id(property_id);
  }
}

/*******************************************************************\

Function: set_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void set_properties(
  goto_functionst &goto_functions,
  const std::list<std::string> &properties)
{
  hash_set_cont<irep_idt, irep_id_hash> property_set;

  for(std::list<std::string>::const_iterator
      it=properties.begin();
      it!=properties.end();
      it++)
    property_set.insert(*it);

  for(goto_functionst::function_mapt::iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    if(!it->second.is_inlined())
      set_properties(it->second.body, property_set);

  if(!property_set.empty())
    throw "property "+id2string(*property_set.begin())+" not found";
}

/*******************************************************************\

Function: label_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void label_properties(goto_functionst &goto_functions)
{
  std::map<irep_idt, unsigned> property_counters;

  for(goto_functionst::function_mapt::iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    if(!it->second.is_inlined())
      label_properties(it->second.body, property_counters);
}

/*******************************************************************\

Function: make_assertions_false

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void make_assertions_false(
  goto_functionst &goto_functions)
{
  for(goto_functionst::function_mapt::iterator
      f_it=goto_functions.function_map.begin();
      f_it!=goto_functions.function_map.end();
      f_it++)
  {
    goto_programt &goto_program=f_it->second.body;
    
    for(goto_programt::instructionst::iterator
        i_it=goto_program.instructions.begin();
        i_it!=goto_program.instructions.end();
        i_it++)
    {
      if(!i_it->is_assert()) continue;
      i_it->guard=false_exprt();
    }
  }
}

