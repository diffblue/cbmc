/*******************************************************************\

Module: Dominators

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

#include <stack>
#include <iostream>

#include "natural_loops.h"

//#define DEBUG

/*******************************************************************\

Function: natural_loopst::compute

  Inputs:

 Outputs:

 Purpose: Finds all back-edges and computes the natural loops

\*******************************************************************/

void natural_loopst::compute(const goto_programt &program)
{
  cfg_dominators(program);
#ifdef DEBUG
  dominators.output(std::cout);
#endif

  // find back-edges m->n
  forall_goto_program_instructions(m_it, program)
  {
    if(m_it->is_backwards_goto())
    {
      for(goto_programt::targetst::const_iterator n_it=m_it->targets.begin();
          n_it!=m_it->targets.end(); ++n_it)
      {
        if((*n_it)->location_number<=m_it->location_number)
        {
          const cfg_dominatorst::nodet &node=
            cfg_dominators.node_map[m_it];
          
#ifdef DEBUG
          std::cout << "Computing loop for " 
                    << m_it->location_number << " -> " 
                    << (*n_it)->location_number << std::endl;
#endif
          if(node.dominators.find(*n_it)!=node.dominators.end())
          {
            compute_natural_loop(m_it, *n_it);
          }
        }
      }
    }
  }
}

/*******************************************************************\

Function: natural_loopst::compute_natural_loop

  Inputs:

 Outputs:

 Purpose: Computes the natural loop for a given back-edge
          (see Muchnick section 7.4)

\*******************************************************************/

void natural_loopst::compute_natural_loop(
  goto_programt::const_targett m, 
  goto_programt::const_targett n)
{
  assert(n->location_number<=m->location_number);
  
  std::stack<goto_programt::const_targett> stack;

  natural_loopt &loop=loop_map[n];

  loop.insert(n);
  loop.insert(m);

  if (n!=m)
    stack.push(m);

  while(!stack.empty())
  {
    goto_programt::const_targett p=stack.top();
    stack.pop();

    const cfg_dominatorst::nodet &node=
      cfg_dominators.node_map[p];

    for(goto_programt::const_targetst::const_iterator
          q_it=node.predecessors.begin();
        q_it!=node.predecessors.end();
        ++q_it)
    {
      goto_programt::const_targett q=*q_it;
      std::pair<natural_loopt::const_iterator, bool> result=loop.insert(q);
      if(result.second)
        stack.push(q);
    }
  }
}

/*******************************************************************\

Function: natural_loopst::output

  Inputs:

 Outputs:

 Purpose: Print all natural loops that were found

\*******************************************************************/

void natural_loopst::output(std::ostream &out) const
{
  for(loop_mapt::const_iterator h_it=loop_map.begin();
      h_it!=loop_map.end(); ++h_it)
  {
    unsigned n=h_it->first->location_number;
    
    out << n << " is head of { ";
    for(natural_loopt::const_iterator l_it=h_it->second.begin();
        l_it!=h_it->second.end();)
    {
      out << (*l_it)->location_number;
      if (++l_it!=h_it->second.end()) 
        out << ", ";
    }
    out << " } " << std::endl;
  }
}

/*******************************************************************\

Function: show_natural_loops

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_natural_loops(const goto_functionst &goto_functions)
{
  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
  {
    std::cout << "*** " << it->first << std::endl;

    natural_loopst natural_loops(it->second.body);
    natural_loops.output(std::cout);
    
    std::cout << std::endl;
  }
}
