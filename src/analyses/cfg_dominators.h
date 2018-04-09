/*******************************************************************\

Module: Compute dominators for CFG of goto_function

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

/// \file
/// Compute dominators for CFG of goto_function

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

template <class P, class T, bool post_dom, bool syntactic=false>
class cfg_dominators_templatet
{
public:
  explicit cfg_dominators_templatet(const namespacet &ns):cfg(ns)
  {
  }

  typedef std::set<T> target_sett;

  struct nodet
  {
    target_sett dominators;
  };

  typedef procedure_local_cfg_baset<nodet, P, T, !syntactic> cfgt;
  cfgt cfg;

  void operator()(P &program);

  T entry_node;

  void output(std::ostream &) const;

protected:
  void initialise(P &program);
  void fixedpoint(P &program);
};

/// Print the result of the dominator computation
template <class P, class T, bool post_dom, bool syntactic>
std::ostream &operator << (
  std::ostream &out,
  const cfg_dominators_templatet<P, T, post_dom, syntactic> &cfg_dominators)
{
  cfg_dominators.output(out);
  return out;
}

/// Compute dominators
template <class P, class T, bool post_dom, bool syntactic>
void cfg_dominators_templatet<P, T, post_dom, syntactic>::operator()(
  P &program)
{
  initialise(program);
  fixedpoint(program);
}

/// Initialises the elements of the fixed point analysis
template <class P, class T, bool post_dom, bool syntactic>
void cfg_dominators_templatet<P, T, post_dom, syntactic>::initialise(
  P &program)
{
  cfg(program);
}

/// Computes the MOP for the dominator analysis
template <class P, class T, bool post_dom, bool syntactic>
void cfg_dominators_templatet<P, T, post_dom, syntactic>::fixedpoint(
  P &program)
{
  std::list<T> worklist;

  if(cfg.nodes_empty(program))
    return;

  if(post_dom)
    entry_node=cfg.get_last_node(program);
  else
    entry_node=cfg.get_first_node(program);
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
    {
      for(const auto &edge : (post_dom ? node.out : node.in))
        if(!cfg[edge.first].dominators.empty())
        {
          node.dominators=cfg[edge.first].dominators;
          node.dominators.insert(current);
          changed=true;
        }
    }

    // compute intersection of predecessors
    for(const auto &edge : (post_dom ? node.out : node.in))
    {
      const target_sett &other=cfg[edge.first].dominators;
      if(other.empty())
        continue;

      typename target_sett::const_iterator n_it=node.dominators.begin();
      typename target_sett::const_iterator o_it=other.begin();

      // in-place intersection. not safe to use set_intersect
      while(n_it!=node.dominators.end() && o_it!=other.end())
      {
        if(*n_it==current)
          ++n_it;
        else if(*n_it<*o_it)
        {
          changed=true;
          node.dominators.erase(n_it++);
        }
        else if(*o_it<*n_it)
          ++o_it;
        else
        {
          ++n_it;
          ++o_it;
        }
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
      for(const auto &edge : (post_dom ? node.in : node.out))
      {
        worklist.push_back(cfg[edge.first].PC);
      }
    }
  }
}

/// Pretty-print a single node in the dominator tree. Supply a specialisation if
/// operator<< is not sufficient.
/// \par parameters: `node` to print and stream `out` to pretty-print it to
template <class T>
void dominators_pretty_print_node(const T &node, std::ostream &out)
{
  out << node;
}

inline void dominators_pretty_print_node(
  const goto_programt::targett& target,
  std::ostream& out)
{
  out << target->code.pretty();
}

/// Print the result of the dominator computation
template <class P, class T, bool post_dom, bool syntactic>
void cfg_dominators_templatet<P, T, post_dom, syntactic>::output(
  std::ostream &out) const
{
  for(const auto &node : cfg.entry_map)
  {
    auto n=node.first;

    dominators_pretty_print_node(n, out);
    if(post_dom)
      out << " post-dominated by ";
    else
      out << " dominated by ";
    bool first=true;
    for(const auto &d : cfg[node.second].dominators)
    {
      if(!first)
        out << ", ";
      first=false;
      dominators_pretty_print_node(d, out);
    }
    out << "\n";
  }
}

typedef cfg_dominators_templatet<
          const goto_programt, goto_programt::const_targett, false, false>
        cfg_dominatorst;

typedef cfg_dominators_templatet<
          const goto_programt, goto_programt::const_targett, true, false>
        cfg_post_dominatorst;

template<>
inline void dominators_pretty_print_node(
  const goto_programt::const_targett &node,
  std::ostream &out)
{
  out << node->location_number;
}

#endif // CPROVER_ANALYSES_CFG_DOMINATORS_H
