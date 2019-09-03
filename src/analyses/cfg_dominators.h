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

/// Dominator graph. This computes a control-flow graph (see \ref cfgt) and
/// decorates it with dominator sets per program point, following
/// "A Simple, Fast Dominance Algorithm" by Cooper et al.
/// Templated over the program type (P) and program point type (T), which need
/// to be supported by \ref cfgt. Can compute either dominators or
/// postdominators depending on template parameter `post_dom`.
/// Use \ref cfg_dominators_templatet::dominates to directly query dominance,
/// or \ref cfg_dominators_templatet::get_node to get the \ref cfgt graph node
/// corresponding to a program point, including the in- and out-edges provided
/// by \ref cfgt as well as the dominator set computed by this class.
/// See also https://en.wikipedia.org/wiki/Dominator_(graph_theory)
template <class P, class T, bool post_dom>
class cfg_dominators_templatet
{
public:
  typedef std::set<std::size_t> target_sett;

  struct nodet
  {
    target_sett dominators;
  };

  typedef cfg_basic_blockst<procedure_local_cfg_baset, nodet, P, T> cfgt;
  cfgt cfg;

  void operator()(P &program);

  /// Get the graph node (which gives dominators, predecessors and successors)
  /// for \p program_point
  const typename cfgt::nodet &get_node(const T &program_point) const
  {
    return cfg.get_node(program_point);
  }

  /// Get the graph node (which gives dominators, predecessors and successors)
  /// for \p program_point
  typename cfgt::nodet &get_node(const T &program_point)
  {
    return cfg.get_node(program_point);
  }

  /// Get the basic-block graph node index for \p program_point
  std::size_t get_node_index(const T &program_point) const
  {
    return cfg.get_node_index(program_point);
  }

  /// Returns true if basic block \p lhs [post]dominates \p rhs
  bool basic_block_dominates(std::size_t lhs, std::size_t rhs) const
  {
    return cfg[rhs].dominators.count(lhs);
  }

  /// Returns true if program point \p lhs [post]dominates \p rhs
  bool dominates_same_block(T lhs, T rhs, std::size_t block) const;

  /// Returns true if program point \p lhs dominates \p rhs.
  /// Note by definition all program points dominate themselves.
  bool dominates(T lhs, T rhs) const
  {
    const auto lhs_block = cfg.entry_map.at(lhs);
    const auto rhs_block = cfg.entry_map.at(rhs);

    if(lhs == rhs)
      return true;

    if(lhs_block != rhs_block)
      return basic_block_dominates(lhs_block, rhs_block);
    else
      return dominates_same_block(lhs, rhs, lhs_block);
  }

  /// Returns true if the basic block \p basic_block_node is reachable
  /// from the entry point. Saves a lookup compared to the overload taking a
  /// program point, so use this overload if you already have the node.
  bool basic_block_reachable(const nodet &basic_block_node) const
  {
    // Dominator analysis walks from the entry point, so a side-effect is to
    // identify unreachable program points (those which don't dominate even
    // themselves).
    return !basic_block_node.dominators.empty();
  }

  /// Returns true if the basic block \p basic_block_node is reachable
  /// from the entry point. Saves a lookup compared to the overload taking a
  /// program point, so use this overload if you already have the node index.
  bool basic_block_reachable(std::size_t block) const
  {
    return basic_block_reachable(cfg[block]);
  }

  /// Returns true if the program point for \p program_point_node is reachable
  /// from the entry point.
  bool program_point_reachable(T program_point) const
  {
    // Dominator analysis walks from the entry point, so a side-effect is to
    // identify unreachable program points (those which don't dominate even
    // themselves).
    return basic_block_reachable(get_node_index(program_point));
  }

  /// Returns the set of dominator blocks for a given basic block, including
  /// itself. The result is a set of indices usable with this class' operator[].
  const target_sett &basic_block_dominators(std::size_t block) const
  {
    return cfg[block].dominators;
  }

  T entry_node;

  void output(std::ostream &) const;

protected:
  void initialise(P &program);
  void fixedpoint(P &program);
};

/// Print the result of the dominator computation
template <class P, class T, bool post_dom>
std::ostream &operator << (
  std::ostream &out,
  const cfg_dominators_templatet<P, T, post_dom> &cfg_dominators)
{
  cfg_dominators.output(out);
  return out;
}

/// Compute dominators
template <class P, class T, bool post_dom>
void cfg_dominators_templatet<P, T, post_dom>::operator()(P &program)
{
  initialise(program);
  fixedpoint(program);
}

/// Initialises the elements of the fixed point analysis
template <class P, class T, bool post_dom>
void cfg_dominators_templatet<P, T, post_dom>::initialise(P &program)
{
  cfg(program);
}

/// Computes the MOP for the dominator analysis
template <class P, class T, bool post_dom>
void cfg_dominators_templatet<P, T, post_dom>::fixedpoint(P &program)
{
  std::list<typename cfgt::node_indext> worklist;

  if(cfgt::nodes_empty(program))
    return;

  if(post_dom)
    entry_node = cfgt::get_last_node(program);
  else
    entry_node = cfgt::get_first_node(program);
  const auto entry_node_index = cfg.get_node_index(entry_node);
  typename cfgt::nodet &n = cfg[entry_node_index];
  n.dominators.insert(entry_node_index);

  for(typename cfgt::edgest::const_iterator
      s_it=(post_dom?n.in:n.out).begin();
      s_it!=(post_dom?n.in:n.out).end();
      ++s_it)
    worklist.push_back(s_it->first);

  while(!worklist.empty())
  {
    // get node from worklist
    const auto current = worklist.front();
    worklist.pop_front();

    bool changed=false;
    typename cfgt::nodet &node = cfg[current];
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
        worklist.push_back(edge.first);
      }
    }
  }
}

template <class P, class T, bool post_dom>
bool cfg_dominators_templatet<P, T, post_dom>::dominates_same_block(
  T lhs,
  T rhs,
  std::size_t block) const
{
  // Special case when the program points belong to the same block: lhs
  // dominates rhs iff it is <= rhs in program order (or the reverse if we're
  // a postdominator analysis)

  for(const auto &instruction : cfg[block].block)
  {
    if(instruction == lhs)
      return !post_dom;
    else if(instruction == rhs)
      return post_dom;
  }

  UNREACHABLE; // Entry map is inconsistent with block members?
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
template <class P, class T, bool post_dom>
void cfg_dominators_templatet<P, T, post_dom>::output(std::ostream &out) const
{
  for(typename cfgt::node_indext i = 0; i < cfg.size(); ++i)
  {
    out << "Block " << dominators_pretty_print_node(cfg[i].block.at(0), out);
    if(post_dom)
      out << " post-dominated by ";
    else
      out << " dominated by ";
    bool first=true;
    for(const auto &d : cfg[i].dominators)
    {
      if(!first)
        out << ", ";
      first=false;
      dominators_pretty_print_node(cfg[d].block.at(0), out);
    }
    out << "\n";
  }
}

typedef cfg_dominators_templatet<
          const goto_programt, goto_programt::const_targett, false>
        cfg_dominatorst;

typedef cfg_dominators_templatet<
          const goto_programt, goto_programt::const_targett, true>
        cfg_post_dominatorst;

template<>
inline void dominators_pretty_print_node(
  const goto_programt::const_targett &node,
  std::ostream &out)
{
  out << node->location_number;
}

#endif // CPROVER_ANALYSES_CFG_DOMINATORS_H
