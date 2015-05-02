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
  nodes.resize(goto_program.instructions.size());

  {  
    node_nrt loc_nr=0;
  
    for(goto_programt::const_targett it=goto_program.instructions.begin();
        it!=goto_program.instructions.end();
        it++, loc_nr++)
    {
      loc_map[it]=loc_nr;
      nodes[loc_nr].t=it;
    }
  }

  for(node_nrt loc_nr=0; loc_nr<nodes.size(); loc_nr++)
  {
    nodet &node=nodes[loc_nr];
    const goto_programt::instructiont &instruction=*node.t;
    
    switch(instruction.type)
    {
    case GOTO:
      if(!instruction.guard.is_true())
        node.successors.push_back(loc_nr+1);
        
      for(goto_programt::targetst::const_iterator
          t_it=instruction.targets.begin();
          t_it!=instruction.targets.end();
          t_it++)
      {
        node_nrt l=loc_map.find(*t_it)->second;
        node.successors.push_back(l); 
      }
      break;
      
    case START_THREAD:
      node.successors.push_back(loc_nr+1);
        
      for(goto_programt::targetst::const_iterator
          t_it=instruction.targets.begin();
          t_it!=instruction.targets.end();
          t_it++)
      {
        node_nrt l=loc_map.find(*t_it)->second;
        node.successors.push_back(l); 
      }
      break;
      
    case RETURN:
      node.successors.push_back(nodes.size()-1);
      break;
      
    case THROW:
    case END_FUNCTION:
    case END_THREAD:
      break; // no successor

    default:
      node.successors.push_back(loc_nr+1);
    }
  }  
}

