/*******************************************************************\

Module: Compute dominators for CFG of goto_function

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

#ifndef CPROVER_ANALYSES_CFG_DOMINATORS_H
#define CPROVER_ANALYSES_CFG_DOMINATORS_H

#include <set>
#include <list>
#include <map>
#include <iosfwd>
#include <cassert>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_program.h>
#include <goto-programs/cfg.h>

template <class P, class T, bool post_dom>
class cfg_dominators_templatet
{
public:
  typedef std::set<T> target_sett;

  struct nodet
  {
    target_sett dominators;
  };

  typedef procedure_local_cfg_baset<nodet, P, T> cfgt;
  cfgt cfg;

  void operator()(P &program);

  target_sett top;
  T entry_node;

  void output(std::ostream &) const;

protected:
  void initialise(P &program);
  void fixedpoint(P &program);
};

/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose: Print the result of the dominator computation

\*******************************************************************/

template <class P, class T, bool post_dom>
std::ostream &operator << (
  std::ostream &out,
  const cfg_dominators_templatet<P, T, post_dom> &cfg_dominators)
{
  cfg_dominators.output(out);
  return out;
}

/*******************************************************************\

Function: operator ()

  Inputs:

 Outputs:

 Purpose: Compute dominators

\*******************************************************************/

template <class P, class T, bool post_dom>
void cfg_dominators_templatet<P, T, post_dom>::operator()(P &program)
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

template <class P, class T, bool post_dom>
void cfg_dominators_templatet<P, T, post_dom>::initialise(P &program)
{
  cfg(program);

  // initialise top element
  for(const auto &node : cfg.entry_map)
    top.insert(cfg[node.second].PC);
}

/*******************************************************************\

Function: cfg_dominators_templatet::fixedpoint

  Inputs:

 Outputs:

 Purpose: Computes the MOP for the dominator analysis

\*******************************************************************/

template <class P, class T, bool post_dom>
void cfg_dominators_templatet<P, T, post_dom>::fixedpoint(P &program)
{
  std::list<T> worklist;

  if(program.instructions.empty())
    return;

  if(post_dom)
    entry_node = --program.instructions.end();
  else
    entry_node = program.instructions.begin();
  typename cfgt::nodet &n=cfg[cfg.entry_map[entry_node]];
  n.dominators.insert(entry_node);

  for(typename cfgt::edgest::const_iterator
      s_it=(post_dom?n.in:n.out).begin();
      s_it!=(post_dom?n.in:n.out).end();
      ++s_it)
    worklist.push_back(cfg[s_it->first].PC);

  while(!worklist.empty())
  {
    // get node from worklist
    T current=worklist.front();
    worklist.pop_front();

    bool changed=false;
    typename cfgt::nodet &node=cfg[cfg.entry_map[current]];
    if(node.dominators.empty())
      for(const auto & edge : (post_dom?node.out:node.in))
        if(!cfg[edge.first].dominators.empty())
        {
          node.dominators=cfg[edge.first].dominators;
          node.dominators.insert(current);
          changed=true;
        }

    // compute intersection of predecessors
    for(const auto & edge : (post_dom?node.out:node.in))
    {
      const target_sett &other=cfg[edge.first].dominators;
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
      {
        if(*n_it==current)
          ++n_it;
        else
        {
          changed=true;
          node.dominators.erase(n_it++);
        }
      }
    }

    if(changed) // fixed point for node reached?
    {
      for(const auto & edge : (post_dom?node.in:node.out))
      {
        worklist.push_back(cfg[edge.first].PC);
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

template <class P, class T, bool post_dom>
void cfg_dominators_templatet<P, T, post_dom>::output(std::ostream &out) const
{
  for(const auto &node : cfg.entry_map)
  {
    unsigned n=node.first->location_number;

    if(post_dom)
      out << n << " post-dominated by ";
    else
      out << n << " dominated by ";
    for(typename target_sett::const_iterator
        d_it=node.second.dominators.begin();
        d_it!=node.second.dominators.end();
       ) // no d_it++
    {
      out << (*d_it)->location_number;
      if (++d_it!=node.second.dominators.end())
        out << ", ";
    }
    out << "\n";
  }
}

typedef cfg_dominators_templatet<const goto_programt, goto_programt::const_targett, false>
        cfg_dominatorst;

typedef cfg_dominators_templatet<const goto_programt, goto_programt::const_targett, true>
        cfg_post_dominatorst;

#endif // CPROVER_ANALYSES_CFG_DOMINATORS_H
