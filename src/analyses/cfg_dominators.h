/*******************************************************************\

Module: Compute dominators for CFG of goto_function

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

/// \file
/// Compute dominators for CFG of goto_function

#ifndef CPROVER_ANALYSES_CFG_DOMINATORS_H
#define CPROVER_ANALYSES_CFG_DOMINATORS_H

#include <util/sharing_map.h>

#include <goto-programs/cfg.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_program.h>

#include <algorithm>
#include <iosfwd>
#include <list>
#include <map>
#include <vector>

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
  /// Set of program points, backed by a copy-on-write sharing map so that
  /// similar sets share most of their representation. Dominator sets of
  /// adjacent program points typically differ in just a single element, so
  /// the sharing keeps the total memory linear-ish in the program size, where
  /// explicit per-node `std::set`s are worst-case quadratic (a straight-line
  /// program of N instructions has dominator sets of total size N^2/2, which
  /// for machine-generated functions with ~100k instructions exhausts tens of
  /// gigabytes of memory).
  class target_sett
  {
  public:
    bool empty() const
    {
      return map.empty();
    }

    std::size_t size() const
    {
      return map.size();
    }

    std::size_t count(const T &t) const
    {
      return map.has_key(t) ? 1 : 0;
    }

    void insert(const T &t)
    {
      if(!map.has_key(t))
        map.insert(t, unitt{});
    }

    /// Invoke \p f for each element of the set, in no particular order.
    void for_each(std::function<void(const T &)> f) const
    {
      map.iterate([&f](const T &k, const unitt &) { f(k); });
    }

    /// Remove all elements that are not also contained in \p other, except
    /// that \p keep is always retained. Return true if any element was
    /// removed. The delta view used here only visits elements in subtrees
    /// that are not shared between the two maps, so intersecting largely
    /// overlapping sets is much cheaper than element-wise iteration.
    bool intersect_with(const target_sett &other, const T &keep)
    {
      typename mapt::delta_viewt delta_view;
      map.get_delta_view(other.map, delta_view, false);

      std::vector<T> to_erase;
      for(const auto &delta_item : delta_view)
      {
        if(!delta_item.is_in_both_maps() && !(delta_item.k == keep))
          to_erase.push_back(delta_item.k);
      }

      for(const auto &item : to_erase)
        map.erase(item);

      return !to_erase.empty();
    }

  protected:
    struct unitt
    {
    };

    struct target_hasht
    {
      /// Program-point hash: program points are either integral (e.g. Java
      /// bytecode offsets) or iterator-like (e.g. goto-program targets), so
      /// hash the value itself or the address of the object it refers to,
      /// respectively.
      template <typename U = T>
      typename std::enable_if<std::is_integral<U>::value, std::size_t>::type
      operator()(const U &t) const
      {
        return std::hash<U>{}(t);
      }

      template <typename U = T>
      typename std::enable_if<!std::is_integral<U>::value, std::size_t>::type
      operator()(const U &t) const
      {
        return std::hash<const void *>{}(&*t);
      }
    };

    typedef sharing_mapt<T, unitt, false, target_hasht> mapt;

    mapt map;
  };

  struct nodet
  {
    target_sett dominators;
  };

  typedef procedure_local_cfg_baset<nodet, P, T> cfgt;
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

  /// Get the graph node index for \p program_point
  typename cfgt::entryt get_node_index(const T &program_point) const
  {
    return cfg.get_node_index(program_point);
  }

  /// Returns true if the program point corresponding to \p rhs_node is
  /// dominated by program point \p lhs. Saves node lookup compared to the
  /// dominates overload that takes two program points, so this version is
  /// preferable if you intend to check more than one potential dominator.
  /// Note by definition all program points dominate themselves.
  bool dominates(T lhs, const nodet &rhs_node) const
  {
    return rhs_node.dominators.count(lhs);
  }

  /// Returns true if program point \p lhs dominates \p rhs.
  /// Note by definition all program points dominate themselves.
  bool dominates(T lhs, T rhs) const
  {
    return dominates(lhs, get_node(rhs));
  }

  /// Returns true if the program point for \p program_point_node is reachable
  /// from the entry point. Saves a lookup compared to the overload taking a
  /// program point, so use this overload if you already have the node.
  bool program_point_reachable(const nodet &program_point_node) const
  {
    // Dominator analysis walks from the entry point, so a side-effect is to
    // identify unreachable program points (those which don't dominate even
    // themselves).
    return !program_point_node.dominators.empty();
  }

  /// Returns true if the program point for \p program_point_node is reachable
  /// from the entry point. Saves a lookup compared to the overload taking a
  /// program point, so use this overload if you already have the node.
  bool program_point_reachable(T program_point) const
  {
    // Dominator analysis walks from the entry point, so a side-effect is to
    // identify unreachable program points (those which don't dominate even
    // themselves).
    return program_point_reachable(get_node(program_point));
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
  std::list<T> worklist;

  if(cfgt::nodes_empty(program))
    return;

  if(post_dom)
    entry_node = cfgt::get_last_node(program);
  else
    entry_node = cfgt::get_first_node(program);
  typename cfgt::nodet &n = cfg.get_node(entry_node);
  n.dominators.insert(entry_node);

  for(typename cfgt::edgest::const_iterator
      s_it=(post_dom?n.in:n.out).begin();
      s_it!=(post_dom?n.in:n.out).end();
      ++s_it)
    worklist.push_back(cfg[s_it->first].PC);

  // A program may have multiple "exit" nodes when self loops or assume(false)
  // instructions are present.
  if(post_dom)
  {
    for(auto &cfg_entry : cfg.entry_map)
    {
      if(cfg[cfg_entry.second].PC == entry_node)
        continue;

      typename cfgt::nodet &n_it = cfg[cfg_entry.second];
      if(
        n_it.out.empty() ||
        (n_it.out.size() == 1 && n_it.out.begin()->first == cfg_entry.second))
      {
        n_it.dominators.insert(cfg[cfg_entry.second].PC);
        for(const auto &predecessor : n_it.in)
          worklist.push_back(cfg[predecessor.first].PC);
      }
    }
  }

  while(!worklist.empty())
  {
    // get node from worklist
    T current=worklist.front();
    worklist.pop_front();

    bool changed=false;
    typename cfgt::nodet &node = cfg.get_node(current);
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

      changed |= node.dominators.intersect_with(other, current);
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
/// \param node: node to print
/// \param out: stream to pretty-print it to
template <class T>
void dominators_pretty_print_node(const T &node, std::ostream &out)
{
  out << node;
}

inline void dominators_pretty_print_node(
  const goto_programt::targett& target,
  std::ostream& out)
{
  out << target->code().pretty();
}

/// Print the result of the dominator computation
template <class P, class T, bool post_dom>
void cfg_dominators_templatet<P, T, post_dom>::output(std::ostream &out) const
{
  for(const auto &node : cfg.entries())
  {
    auto n=node.first;

    dominators_pretty_print_node(n, out);
    if(post_dom)
      out << " post-dominated by ";
    else
      out << " dominated by ";

    std::vector<T> sorted_dominators;
    cfg[node.second].dominators.for_each([&sorted_dominators](const T &d)
                                         { sorted_dominators.push_back(d); });
    std::sort(
      sorted_dominators.begin(),
      sorted_dominators.end(),
      typename P::target_less_than{});

    bool first=true;
    for(const auto &d : sorted_dominators)
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
