/*******************************************************************\

Module: Dominators

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

#include <iostream>

#include "cfg_dominators.h"

/*******************************************************************\

Function: cfg_dominatorst::initialise

  Inputs:

 Outputs:

 Purpose: Initialises the elements of the fixed point analysis

\*******************************************************************/

void cfg_dominatorst::initialise(const goto_programt& program)
{
  construct_cfg(program);

  // initialise top element
  for(node_mapt::const_iterator e_it=node_map.begin();
      e_it!=node_map.end(); ++e_it)
    top.insert(e_it->first);
  
  // initialise all entries to top
  for(node_mapt::iterator e_it=node_map.begin();
      e_it!=node_map.end(); ++e_it)
    e_it->second.dominators.insert(top.begin(), top.end()); 
}

/*******************************************************************\

Function: cfg_dominatorst::construct_cfg

  Inputs:

 Outputs:

 Purpose: Initialises the predecessor and successor sets

\*******************************************************************/

void cfg_dominatorst::construct_cfg(const goto_programt &program)
{
  forall_goto_program_instructions(it, program)
    construct_cfg(program, it);
}

/*******************************************************************\

Function: cfg_dominatorst::construct_cfg

  Inputs:

 Outputs:

 Purpose: Initialises the predecessor and successor sets

\*******************************************************************/

void cfg_dominatorst::construct_cfg(
  const goto_programt &program, 
  goto_programt::const_targett PC)
{
  nodet &node=node_map[PC];
  node.PC=PC;
  
  program.get_successors(PC, node.successors);

  // now do backward edges
  for(goto_programt::const_targetst::const_iterator
        s_it=node.successors.begin();
      s_it!=node.successors.end();
      s_it++)
  {
    node_map[*s_it].predecessors.push_back(node.PC);
  }

}

/*******************************************************************\

Function: cfg_dominatorst::fixedpoint

  Inputs:

 Outputs:

 Purpose: Computes the MOP for the dominator analysis

\*******************************************************************/

void cfg_dominatorst::fixedpoint(const goto_programt &program)
{
  goto_programt::const_targetst worklist;

  entry_node = program.instructions.begin();
  worklist.push_back(entry_node);

  while(worklist.size())
  {
    // get node from worklist
    goto_programt::const_targett current=worklist.front();
    worklist.pop_front();

    nodet &node=node_map[current];

    // compute intersection of predecessors
    const_target_sett result;
    
    for(goto_programt::const_targetst::const_iterator 
          p_it=node.predecessors.begin();
        p_it!=node.predecessors.end();
        ++p_it)
    {   
      if(p_it==node.predecessors.begin())
      {
        result=node_map[*p_it].dominators;
        continue;
      }
      else
      {
        const const_target_sett &other=node_map[*p_it].dominators;
        const_target_sett::const_iterator r_it=result.begin();
        const_target_sett::const_iterator o_it=other.begin();

        // in-place intersection. not safe to use set_intersect
        while(r_it!=result.end() && o_it!=other.end())
        {
          if(*r_it<*o_it) result.erase(r_it++);
          else if(*o_it<*r_it) ++o_it;
          else { ++r_it; ++o_it; }
        }
      }
    }

    result.insert(current);

    if(node.dominators!=result) // fixed point for node reached?
    {
      node.dominators=result;
      for(goto_programt::const_targetst::const_iterator 
            s_it=node.successors.begin();
          s_it!=node.successors.end();
          ++s_it)
      {
        worklist.push_back(*s_it);
      }
    }
  }
}

/*******************************************************************\

Function: cfg_dominatorst::output

  Inputs:

 Outputs:

 Purpose: Print the result of the dominator computation

\*******************************************************************/

void cfg_dominatorst::output(std::ostream &out) const
{
  for(node_mapt::const_iterator it=node_map.begin();
      it!=node_map.end(); ++it)
  {
    unsigned n=it->first->location_number;
    
    out << n << " dominated by ";
    for(const_target_sett::const_iterator d_it=it->second.dominators.begin();
        d_it!=it->second.dominators.end();)
    {
      out << (*d_it)->location_number;
      if (++d_it!=it->second.dominators.end()) 
        out << ", ";
    }
    out << std::endl;
  }
}

/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose: Print the result of the dominator computation

\*******************************************************************/

std::ostream &operator << (
  std::ostream &out,
  const cfg_dominatorst &cfg_dominators)
{
  cfg_dominators.output(out);
  return out;
}

