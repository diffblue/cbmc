/*******************************************************************\

Module: Compute dominators for CFG of goto_function

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

#ifndef CPROVER_CFG_DOMINATORS_H
#define CPROVER_CFG_DOMINATORS_H

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
  void operator()(P &program, T start, bool start_dominates_itself=true);

  target_sett top;
  T entry_node;

  void output(std::ostream &) const;

protected:
  void initialise(P &program);
  void fixedpoint(P &program);
  void fixedpoint(P &program, T start, bool start_dominates_itself=true);
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

Function: operator ()

  Inputs:

 Outputs:

 Purpose: Compute dominators

\*******************************************************************/

template <class P, class T, bool post_dom>
void cfg_dominators_templatet<P, T, post_dom>::operator()(
  P &program,
  T start,
  bool start_dominates_itself)
{
  initialise(program);
  fixedpoint(program, start, start_dominates_itself);
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
  for(typename cfgt::entry_mapt::const_iterator
      e_it=cfg.entry_map.begin();
      e_it!=cfg.entry_map.end(); ++e_it)
    top.insert(cfg[e_it->second].PC);
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
  if(post_dom)
    fixedpoint(program, --program.instructions.end());
  else
    fixedpoint(program, program.instructions.begin());
}

/*******************************************************************\

Function: cfg_dominators_templatet::fixedpoint

  Inputs:

 Outputs:

 Purpose: Computes the MOP for the dominator analysis

\*******************************************************************/

template <class P, class T, bool post_dom>
void cfg_dominators_templatet<P, T, post_dom>::fixedpoint(
  P &program,
  T start,
  bool start_dominates_itself)
{
  std::list<T> worklist;

  if(program.instructions.empty())
    return;

  entry_node=start;

  typename cfgt::nodet &n=cfg[cfg.entry_map[entry_node]];

  if (start_dominates_itself)
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
      for(typename cfgt::edgest::const_iterator 
          p_it=(post_dom?node.out:node.in).begin();
          !changed && p_it!=(post_dom?node.out:node.in).end();
          ++p_it)
        if(!cfg[p_it->first].dominators.empty())
        {
          node.dominators=cfg[p_it->first].dominators;
          node.dominators.insert(current);
          changed=true;
        }

    // compute intersection of predecessors
    for(typename cfgt::edgest::const_iterator 
          p_it=(post_dom?node.out:node.in).begin();
        p_it!=(post_dom?node.out:node.in).end();
        ++p_it)
    {   
      const target_sett &other=cfg[p_it->first].dominators;
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
      for(typename cfgt::edgest::const_iterator 
            s_it=(post_dom?node.in:node.out).begin();
          s_it!=(post_dom?node.in:node.out).end();
          ++s_it)
      {
        worklist.push_back(cfg[s_it->first].PC);
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
  for(typename cfgt::entry_mapt::const_iterator
      it=cfg.entry_map.begin();
      it!=cfg.entry_map.end(); ++it)
  {
    unsigned n=it->first->location_number;
    
    if(post_dom)
      out << n << " post-dominated by ";
    else
      out << n << " dominated by ";

    int entry_num=it->second;
    const nodet &node=cfg[entry_num];

    for(typename target_sett::const_iterator d_it=node.dominators.begin();
        d_it!=node.dominators.end();)
    {
      bool has_location;
      has_location=cfg.entry_map.find(*d_it)!=cfg.entry_map.end();
      assert(has_location);

      out << (*d_it)->location_number;

      d_it++;
      if(d_it!=node.dominators.end())
        out << ", ";
    }
    out << "\n";
  }
}

typedef cfg_dominators_templatet<const goto_programt, goto_programt::const_targett, false>
        cfg_dominatorst;

typedef cfg_dominators_templatet<const goto_programt, goto_programt::const_targett, true>
        cfg_post_dominatorst;

#endif
