/*******************************************************************\

Module: CFG for One Function

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#if 0
#include <iterator>
#include <algorithm>

#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/expr_util.h>

#include <ansi-c/c_types.h>
#include <langapi/language_util.h>

#endif

#include "local_cfg.h"

/*******************************************************************\

Function: local_cfgt::build

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void local_cfgt::build(const goto_programt &goto_program)
{
  locs.resize(goto_program.instructions.size());

  {  
    unsigned loc_nr=0;
  
    for(goto_programt::const_targett it=goto_program.instructions.begin();
        it!=goto_program.instructions.end();
        it++, loc_nr++)
    {
      loc_map[it]=loc_nr;
      locs[loc_nr].t=it;
    }
  }

  for(unsigned loc_nr=0; loc_nr<locs.size(); loc_nr++)
  {
    loct &loc=locs[loc_nr];
    const goto_programt::instructiont &instruction=*loc.t;
    
    switch(instruction.type)
    {
    case GOTO:
      if(!instruction.guard.is_true())
        loc.successors.push_back(loc_nr+1);
        
      for(goto_programt::targetst::const_iterator
          t_it=instruction.targets.begin();
          t_it!=instruction.targets.end();
          t_it++)
      {
        unsigned l=loc_map.find(*t_it)->second;
        loc.successors.push_back(l); 
      }
      break;
      
    case START_THREAD:
      loc.successors.push_back(loc_nr+1);
        
      for(goto_programt::targetst::const_iterator
          t_it=instruction.targets.begin();
          t_it!=instruction.targets.end();
          t_it++)
      {
        unsigned l=loc_map.find(*t_it)->second;
        loc.successors.push_back(l); 
      }
      break;
      
    case RETURN:
      loc.successors.push_back(locs.size()-1);
      break;
      
    case THROW:
    case END_FUNCTION:
    case END_THREAD:
      break; // no successor

    default:
      loc.successors.push_back(loc_nr+1);
    }
  }  
}

