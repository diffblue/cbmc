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
  nodet &n=node_map[entry_node];
  n.dominators.insert(entry_node);
  for(goto_programt::const_targetst::const_iterator 
      s_it=n.successors.begin();
      s_it!=n.successors.end();
      ++s_it)
    worklist.push_back(*s_it);

  while(!worklist.empty())
  {
    // get node from worklist
    goto_programt::const_targett current=worklist.front();
    worklist.pop_front();

    bool changed=false;
    nodet &node=node_map[current];
    if(node.dominators.empty())
      for(goto_programt::const_targetst::const_iterator 
          p_it=node.predecessors.begin();
          !changed && p_it!=node.predecessors.end();
          ++p_it)
        if(!node_map[*p_it].dominators.empty())
        {
          node.dominators=node_map[*p_it].dominators;
          node.dominators.insert(current);
          changed=true;
        }

    // compute intersection of predecessors
    for(goto_programt::const_targetst::const_iterator 
          p_it=node.predecessors.begin();
        p_it!=node.predecessors.end();
        ++p_it)
    {   
      const const_target_sett &other=node_map[*p_it].dominators;
      const_target_sett::const_iterator n_it=node.dominators.begin();
      const_target_sett::const_iterator o_it=other.begin();

      // in-place intersection. not safe to use set_intersect
      while(n_it!=node.dominators.end() && o_it!=other.end())
      {
        if(*n_it==current) ++n_it;
        else if(*n_it<*o_it) { changed=true; node.dominators.erase(n_it++); }
        else if(*o_it<*n_it) ++o_it;
        else { ++n_it; ++o_it; }
      }
    }

    if(changed) // fixed point for node reached?
    {
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

