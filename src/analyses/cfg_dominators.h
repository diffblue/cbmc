/*******************************************************************\

Module: Compute dominators for CFG of goto_function

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

#ifndef CPROVER_CFG_DOMINATORS_H
#define CPROVER_CFG_DOMINATORS_H

#include <set>
#include <list>
#include <map>
#include <ostream>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_program.h>

template<class P, class T>
class cfg_dominators_templatet
{
public:
  typedef std::set<T> target_sett;

  struct nodet
  {
    target_sett dominators;
    std::list<T> successors, predecessors;

    T PC;
  };

  typedef std::map<T, nodet> node_mapt;
  node_mapt node_map;

  void operator()(P &program);

  target_sett top;
  T entry_node;

  void output(std::ostream&) const;

protected:
  void initialise(P &program);
  void construct_cfg(P &program);
  void construct_cfg(P &program, T PC);
  void fixedpoint(P &program);
};

/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose: Print the result of the dominator computation

\*******************************************************************/

template <class P, class T>
std::ostream &operator << (
  std::ostream &out,
  const cfg_dominators_templatet<P, T> &cfg_dominators)
{
  cfg_dominators.output(out);
  return out;
}


template<class P, class T>
void cfg_dominators_templatet<P, T>::operator()(P &program)
{
  initialise(program);
  fixedpoint(program);
}

/*******************************************************************\

Function: cfg_dominators_templatet::initialise

  Inputs:

 Outputs:

 Purpose: Initialises the elements of the fixed point analysis

\*******************************************************************/

template<class P, class T>
void cfg_dominators_templatet<P, T>::initialise(P &program)
{
  construct_cfg(program);

  // initialise top element
  for(typename node_mapt::const_iterator e_it=node_map.begin();
      e_it!=node_map.end(); ++e_it)
    top.insert(e_it->first);
}

/*******************************************************************\

Function: cfg_dominators_templatet::construct_cfg

  Inputs:

 Outputs:

 Purpose: Initialises the predecessor and successor sets

\*******************************************************************/

template<class P, class T>
void cfg_dominators_templatet<P, T>::construct_cfg(P &program)
{
  for (T it = program.instructions.begin();
       it != program.instructions.end();
       ++it)
  {
    construct_cfg(program, it);
  }
}

/*******************************************************************\

Function: cfg_dominators_templatet::construct_cfg

  Inputs:

 Outputs:

 Purpose: Initialises the predecessor and successor sets

\*******************************************************************/

template <class P, class T>
void cfg_dominators_templatet<P, T>::construct_cfg(P &program, T PC)
{
  nodet &node=node_map[PC];
  node.PC=PC;
  
  program.get_successors(PC, node.successors);

  // now do backward edges
  for(typename std::list<T>::const_iterator
        s_it=node.successors.begin();
      s_it!=node.successors.end();
      s_it++)
  {
    node_map[*s_it].predecessors.push_back(node.PC);
  }

}

/*******************************************************************\

Function: cfg_dominators_templatet::fixedpoint

  Inputs:

 Outputs:

 Purpose: Computes the MOP for the dominator analysis

\*******************************************************************/

template<class P, class T>
void cfg_dominators_templatet<P, T>::fixedpoint(P &program)
{
  std::list<T> worklist;

  entry_node = program.instructions.begin();
  nodet &n=node_map[entry_node];
  n.dominators.insert(entry_node);
  for(typename std::list<T>::const_iterator 
      s_it=n.successors.begin();
      s_it!=n.successors.end();
      ++s_it)
    worklist.push_back(*s_it);

  while(!worklist.empty())
  {
    // get node from worklist
    T current=worklist.front();
    worklist.pop_front();

    bool changed=false;
    nodet &node=node_map[current];
    if(node.dominators.empty())
      for(typename std::list<T>::const_iterator 
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
    for(typename std::list<T>::const_iterator 
          p_it=node.predecessors.begin();
        p_it!=node.predecessors.end();
        ++p_it)
    {   
      const target_sett &other=node_map[*p_it].dominators;
      if(other.empty())
        continue;

      typename target_sett::const_iterator n_it=node.dominators.begin();
      typename target_sett::const_iterator o_it=other.begin();

      // in-place intersection. not safe to use set_intersect
      while(n_it!=node.dominators.end() && o_it!=other.end())
      {
        if(*n_it==current) ++n_it;
        else if(*n_it<*o_it) { changed=true; node.dominators.erase(n_it++); }
        else if(*o_it<*n_it) ++o_it;
        else { ++n_it; ++o_it; }
      }
      while(n_it!=node.dominators.end())
        if(*n_it==current)
          ++n_it;
        else
        {
          changed=true;
          node.dominators.erase(n_it++);
        }
    }

    if(changed) // fixed point for node reached?
    {
      for(typename std::list<T>::const_iterator 
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

Function: cfg_dominators_templatet::output

  Inputs:

 Outputs:

 Purpose: Print the result of the dominator computation

\*******************************************************************/

template <class P, class T>
void cfg_dominators_templatet<P, T>::output(std::ostream &out) const
{
  for(typename node_mapt::const_iterator it=node_map.begin();
      it!=node_map.end(); ++it)
  {
    unsigned n=it->first->location_number;
    
    out << n << " dominated by ";
    for(typename target_sett::const_iterator d_it=it->second.dominators.begin();
        d_it!=it->second.dominators.end();)
    {
      out << (*d_it)->location_number;
      if (++d_it!=it->second.dominators.end()) 
        out << ", ";
    }
    out << std::endl;
  }
}

typedef cfg_dominators_templatet<const goto_programt, goto_programt::const_targett>
        cfg_dominatorst;

#endif
