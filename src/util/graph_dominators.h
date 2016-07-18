/*******************************************************************\

Module: Compute dominators for Graph

Author: Georg Weissenbacher, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_GRAPH_DOMINATORS_H
#define CPROVER_GRAPH_DOMINATORS_H

#include <iostream>
#include <set>
#include <list>
#include <map>
#include <iosfwd>
#include <cassert>

template <class G, bool post_dom>
class graph_dominators_templatet
{
public:
  typedef std::set<typename G::node_indext> target_sett;
  typedef std::map<typename G::node_indext,target_sett> dominatorst;
  dominatorst dominators;

  void operator()(G &graph, typename G::node_indext entry_node);

  typename G::node_indext entry_node;

  void output(std::ostream &) const;

  static bool set_intersect(
    target_sett &s, const target_sett& t,
    typename G::node_indext current);

protected:
  void initialise(G &graph);
  void fixedpoint(G &graph);
};

/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose: Print the result of the dominator computation

\*******************************************************************/

template <class G, bool post_dom>
std::ostream &operator << (
  std::ostream &out,
  const graph_dominators_templatet<G, post_dom> &graph_dominators)
{
  graph_dominators.output(out);
  return out;
}

/*******************************************************************\

Function: operator ()

  Inputs:

 Outputs:

 Purpose: Compute dominators

\*******************************************************************/

template <class G, bool post_dom>
void graph_dominators_templatet<G, post_dom>::operator()(G &graph, typename G::node_indext _entry_node)
{
  entry_node = _entry_node;
  initialise(graph);
  fixedpoint(graph);
}

/*******************************************************************\

Function: graph_dominators_templatet::initialise

  Inputs:

 Outputs:

 Purpose: Initialises the elements of the fixed point analysis

\*******************************************************************/

template <class G, bool post_dom>
void graph_dominators_templatet<G, post_dom>::initialise(G &graph)
{
  dominators.clear();
}

/*******************************************************************\

Function: graph_dominators_templatet::fixedpoint

  Inputs:

 Outputs:

 Purpose: Computes the MOP for the dominator analysis

\*******************************************************************/

template <class G, bool post_dom>
void graph_dominators_templatet<G, post_dom>::fixedpoint(G &graph)
{
  std::list<typename G::node_indext> worklist;

  if(graph.size()==0)
    return;

  typename G::nodet n = graph[entry_node];  
  dominators[entry_node].insert(entry_node);

  for(typename G::edgest::const_iterator 
      s_it=(post_dom?n.in:n.out).begin();
      s_it!=(post_dom?n.in:n.out).end();
      ++s_it)
    worklist.push_back(s_it->first);

  while(!worklist.empty())
  {
    // get node from worklist
    typename G::node_indext current=worklist.front();
    worklist.pop_front();

    bool changed=false;
    typename G::nodet &node=graph[current];
    if(dominators[current].empty())
      for(typename G::edgest::const_iterator 
          p_it=(post_dom?node.out:node.in).begin();
          !changed && p_it!=(post_dom?node.out:node.in).end();
          ++p_it)
        if(!dominators[p_it->first].empty())
        {
          dominators[current]=dominators[p_it->first];
          dominators[current].insert(current);
          changed=true;
        }

    // compute intersection of predecessors
    for(typename G::edgest::const_iterator 
          p_it=(post_dom?node.out:node.in).begin();
        p_it!=(post_dom?node.out:node.in).end();
        ++p_it)
    {   
      const target_sett &other=dominators[p_it->first];
      if(other.empty())
        continue;

      changed = set_intersect(dominators[current],other,current)
	|| changed;
    }

    if(changed) // fixed point for node reached?
    {
      for(typename G::edgest::const_iterator 
            s_it=(post_dom?node.in:node.out).begin();
          s_it!=(post_dom?node.in:node.out).end();
          ++s_it)
      {
        worklist.push_back(s_it->first);
      }
    }
  }
}

/*******************************************************************\

Function: graph_dominators_templatet::output

  Inputs:

 Outputs:

 Purpose: Print the result of the dominator computation

\*******************************************************************/

template <class G, bool post_dom>
void graph_dominators_templatet<G, post_dom>::output(std::ostream &out) const
{
  for(typename dominatorst::const_iterator it = dominators.begin();
      it != dominators.end(); ++it)
  {
    if(post_dom)
      out << it->first << " post-dominated by ";
    else
      out << it->first << " dominated by ";
    for(typename target_sett::const_iterator d_it = it->second.begin();
        d_it!=it->second.end();)
    {
      out << *d_it;
      if (++d_it!=it->second.end()) 
        out << ", ";
    }
    out << "\n";
  }
}

/*******************************************************************\

Function: graph_dominators_templatet::set_intersect

  Inputs: 

 Outputs: returns true if set s changed

 Purpose: in-place intersection

\*******************************************************************/

template <class G, bool post_dom>
bool graph_dominators_templatet<G, post_dom>::set_intersect(
  target_sett &s, const target_sett& t,
  typename G::node_indext current)
{
  typename target_sett::const_iterator n_it=s.begin();
  typename target_sett::const_iterator o_it=t.begin();
  bool changed = false;

  // in-place intersection. not safe to use set_intersect
  while(n_it!=s.end() && o_it!=t.end())
  {
    if(*n_it==current) ++n_it;
    else if(*n_it<*o_it) { changed=true; s.erase(n_it++); }
    else if(*o_it<*n_it) ++o_it;
    else { ++n_it; ++o_it; }
  }

  while(n_it!=s.end())
  {
    if(*n_it==current)
      ++n_it;
    else
    {
      changed=true;
      s.erase(n_it++);
    }
  }
  return changed;
}

#endif

