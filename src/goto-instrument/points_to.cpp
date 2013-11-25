/*******************************************************************\

Module: Field-sensitive, location-insensitive points-to analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "points_to.h"

/*******************************************************************\

Function: points_tot::fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void points_tot::fixedpoint()
{
  // this loop iterates until fixed-point

  bool added;

  do
  {
    added=false;
  
    for(cfgt::entry_mapt::iterator
        e_it=cfg.entry_map.begin();
        e_it!=cfg.entry_map.end();
        e_it++)
    {
      if(transform(&e_it->second))
        added=true;
    }
  }
  while(added);
}

/*******************************************************************\

Function: points_tot::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void points_tot::output(std::ostream &out) const
{
  for(value_mapt::const_iterator
      v_it=value_map.begin();
      v_it!=value_map.end();
      v_it++)
  {
    out << v_it->first << ":";

    for(object_id_sett::const_iterator
        o_it=v_it->second.begin();
        o_it!=v_it->second.end();
        o_it++)
    {
      out << " " << *o_it;
    }
    
    out << std::endl;
  }
}

/*******************************************************************\

Function: points_tot::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool points_tot::transform(cfgt::iterator e)
{
  bool result=false;
  const goto_programt::instructiont &instruction=*(e->PC);

  switch(instruction.type)
  {
  case RETURN:
    // TODO
    break;
    
  case ASSIGN:
    {
      // const code_assignt &code_assign=to_code_assign(instruction.code);
      
    }    
    break;
  
  case FUNCTION_CALL:
    // these are like assignments for the arguments
    break;
  
  default:;
  }
  
  return result;
}
