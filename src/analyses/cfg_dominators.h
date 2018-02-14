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
#include <algorithm>
#include <stack>
#include <tuple>
#include <type_traits>
#include <iterator>
#include <memory>
#include <limits>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_program.h>
#include <goto-programs/cfg.h>

/// Dominator tree
/// Node indices are 0-based here (unlike in the internal data structures of
/// the algorithm).
template <typename T, typename node_indext>
struct dominators_datat
{
  explicit dominators_datat(std::size_t size)
    : data(size), immediate_dominator(size)
  {
  }
  dominators_datat(
    std::vector<T> data,
    std::vector<node_indext> immediate_dominator)
    : data(data), immediate_dominator(immediate_dominator)
  {
  }

  /// Maps node to T
  std::vector<T> data;

  /// Maps node to its immediate dominator
  std::vector<node_indext> immediate_dominator;
};

/// An immutable set of dominators. Constant memory usage and creation time.
/// Immutability is necessary because the structure uses sharing.
template <typename T, typename node_indext>
class dominatorst
{
public:
  using datat = dominators_datat<T, node_indext>;
  static const node_indext npos;

private:
  std::shared_ptr<datat> dominators_data;
  node_indext node_index;
  mutable std::size_t cached_distance;

public:
  /// Create an empty set
  /// Note: Only unreachable nodes should be assigned empty sets after the
  /// algorithm completes
  dominatorst() : dominators_data(nullptr), node_index(npos), cached_distance(0)
  {
  }

  /// Create the dominators set of node_index
  dominatorst(std::shared_ptr<datat> dominators_data, node_indext node_index)
    : dominators_data(dominators_data),
      node_index(node_index),
      cached_distance(npos)
  {
  }

  dominatorst(const dominatorst &other)
    : dominators_data(other.dominators_data),
      node_index(other.node_index),
      cached_distance(other.cached_distance)
  {
  }

  dominatorst &operator=(const dominatorst &rhs)
  {
    dominators_data = rhs.dominators_data;
    node_index = rhs.node_index;
    cached_distance = rhs.cached_distance;
    return *this;
  }

  class dominatorst_iteratort
    : public std::iterator<std::forward_iterator_tag, T>
  {
  public:
    using parentt = const datat *;
    using elemt = const T;

  private:
    parentt data;
    node_indext current_index;

  public:
    dominatorst_iteratort(parentt cfg_dominators, node_indext current_index)
      : data(cfg_dominators), current_index(current_index)
    {
    }

    dominatorst_iteratort &operator++()
    {
      INVARIANT(
        current_index != npos, "Shouldn't try to increment end-iterator");
      current_index = data->immediate_dominator[current_index];
      return *this;
    }

    dominatorst_iteratort operator++(int)
    {
      INVARIANT(
        current_index != npos, "Shouldn't try to post-increment end-iterator");
      node_indext tmp = current_index;
      ++(*this);
      return dominatorst_iteratort(data, tmp);
    }

    const elemt *get() const
    {
      INVARIANT(
        current_index != npos, "Shouldn't try to dereference end-iterator");
      return &data->data[current_index];
    }

    const elemt &operator*() const
    {
      return *get();
    }

    const elemt *operator->() const
    {
      return get();
    }

    bool operator!=(const dominatorst_iteratort &other) const
    {
      INVARIANT(
        data == other.data, "iterators from different sets are not comparable");
      return current_index != other.current_index;
    }

    bool operator==(const dominatorst_iteratort &other) const
    {
      return !(*this != other);
    }
  };

  using const_iterator = dominatorst_iteratort;

  const_iterator begin() const
  {
    return const_iterator(dominators_data.get(), node_index);
  }

  const_iterator cbegin() const
  {
    return begin();
  }

  const_iterator end() const
  {
    return const_iterator(dominators_data.get(), npos);
  }

  const_iterator cend() const
  {
    return end();
  }

  /// Return an iterator node if node is in this dominators set, end() otherwise
  /// Note: O(n), when making many queries against the same set it is probably
  /// worth copying into a std::set
  const_iterator find(const T &node) const
  {
    std::less<T> less;
    // FIXME This works around a bug in other parts of the code in particular,
    // dependence_graph.cpp, where iterators to different lists than those that
    // are stored in this set are passed to find. The Debug libstdc++ will
    // (correctly!) run into an assertion failure using std::find. std::less for
    // some reason doesn't trigger this assertion failure, so we use this as an
    // ugly workaround until that code is fixed.

    // NOLINTNEXTLINE
    return std::find_if(cbegin(), cend(), [&](const T &other_node) {
      return !less(node, other_node) && !less(other_node, node);
    });
  }

  /// The size of the set. Linear time on the first call, constant after that.
  std::size_t size() const
  {
    if(cached_distance == npos)
    {
      cached_distance = std::distance(begin(), end());
    }
    return cached_distance;
  }

  bool empty() const
  {
    return begin() == end();
  }
};

template <typename T, typename node_indext>
const node_indext
  dominatorst<T, node_indext>::npos = std::numeric_limits<node_indext>::max();

/// Dominators for each instruction in a goto program
template <class P, class T, bool post_dom>
class cfg_dominators_templatet
{
public:
  using node_indext = graph_nodet<>::node_indext;
  using target_sett = dominatorst<T, node_indext>;

  struct nodet
  {
    target_sett dominators;
  };

  typedef procedure_local_cfg_baset<nodet, P, T> cfgt;
  cfgt cfg;

  void operator()(P &program);

  T entry_node;

  void output(std::ostream &) const;

protected:
  void initialise(P &program);

  struct fixedpointt
  {
    explicit fixedpointt(cfg_dominators_templatet &cfg_dominators)
      : cfg_dominators(cfg_dominators),
        dfs_counter(0),
        // Data structures have size cfg.size() + 1 as node indices are 1-based
        // to match the paper of Lengauer/Tarjan.
        parent(cfg_dominators.cfg.size() + 1),
        vertex(cfg_dominators.cfg.size() + 1),
        dom(cfg_dominators.cfg.size() + 1),
        semi(cfg_dominators.cfg.size() + 1),
        bucket(cfg_dominators.cfg.size() + 1),
        ancestor(cfg_dominators.cfg.size() + 1),
        label(cfg_dominators.cfg.size() + 1),
        size(cfg_dominators.cfg.size() + 1),
        child(cfg_dominators.cfg.size() + 1)
    {
    }

    void fixedpoint(P &program);

  private:
    cfg_dominators_templatet &cfg_dominators;
    node_indext dfs_counter;

    /// Maps node to its parent in the DFS-generated spanning tree
    std::vector<node_indext> parent;

    /// Maps number to node (according to the DFS numbering)
    std::vector<node_indext> vertex;

    /// Maps node to its immediate dominator
    std::vector<node_indext> dom;

    /// Maps node to its semi-dominator (as defined by Lengauer/Tarjan)
    /// A semidominator of a node w is the minimum node v (according to the DFS
    /// numbering) for which there is a path from v to w such that all nodes
    /// occuring on that path (other than v, w) have a larger number than w
    /// (according to the DFS numbering)
    std::vector<node_indext> semi;

    /// Maps node to the set of nodes of which it is the semi-dominator
    std::vector<std::set<node_indext>> bucket;

    // Used by link() and eval(), which are used to create and query
    // an auxiliary data structure which is a forest that is contained
    // in the DFS spanning tree.
    std::vector<node_indext> ancestor;
    std::vector<node_indext> label;
    std::vector<node_indext> size;
    std::vector<node_indext> child;

    T get_entry_node(P &program)
    {
      if(post_dom)
      {
        return cfg_dominators.cfg.get_last_node(program);
      }
      else
      {
        return cfg_dominators.cfg.get_first_node(program);
      }
    };

    /// DFS numbering
    /// Number nodes in the order in which they are reached during a DFS,
    /// intialize data structures
    void dfs(node_indext root)
    {
      struct dfs_statet
      {
        node_indext parent;
        node_indext current;
      };
      std::stack<dfs_statet> work;
      work.push({0, root});
      while(!work.empty())
      {
        auto state = work.top();
        work.pop();
        node_indext v = state.current;
        if(semi[v] == 0)
        {
          // Initialize data structures
          parent[v] = state.parent;
          semi[v] = ++dfs_counter;
          vertex[dfs_counter] = label[v] = v;
          ancestor[v] = child[v] = 0;
          size[v] = 1;
          // Explore children
          for_each_successor(v, [&](node_indext w) { work.push({v, w}); });
        }
      }
    }

    /// Compress path from v to the root in the tree of the forest that contains
    /// v, by directly attaching nodes to the root
    void compress(node_indext v)
    {
      if(ancestor[ancestor[v]] != 0)
      {
        compress(ancestor[v]);
        if(semi[label[ancestor[v]]] < semi[label[v]])
        {
          label[v] = label[ancestor[v]];
        }
        ancestor[v] = ancestor[ancestor[v]];
      }
    }

    /// Return node with minimum semidominator on the path from the root of the
    /// tree in the forest containing v to v, and compress path
    node_indext eval(node_indext v)
    {
      if(ancestor[v] == 0)
      {
        return label[v];
      }
      compress(v);
      if(semi[label[ancestor[v]]] >= semi[label[v]])
      {
        return label[v];
      }
      return label[ancestor[v]];
    }

    /// Add an edge to the forest
    /// \param v: source node of edge
    /// \param w: target node of edge
    void link(node_indext v, node_indext w)
    {
      node_indext s = w;
      while(semi[label[w]] < semi[label[child[s]]])
      {
        if(size[s] + size[child[child[s]]] >= 2 * size[child[s]])
        {
          ancestor[child[s]] = s;
          child[s] = child[child[s]];
        }
        else
        {
          size[child[s]] = size[s];
          s = ancestor[s] = child[s];
        }
      }
      label[s] = label[w];
      size[v] = size[v] + size[w];
      if(size[v] < 2 * size[w])
      {
        std::swap(s, child[v]);
      }
      while(s != 0)
      {
        ancestor[s] = v;
        s = child[s];
      }
    }

    /// Fill output data structures
    void assign_dominators(node_indext root)
    {
      // Fill dominator tree output data structure
      auto dominators_data = std::make_shared<typename target_sett::datat>(
        cfg_dominators.cfg.size());
      for(node_indext i = 0; i < cfg_dominators.cfg.size(); ++i)
      {
        dominators_data->immediate_dominator[i] = dom[i + 1] - 1;
        dominators_data->data[i] = cfg_dominators.cfg[i].PC;
      }

      // Assign immediate dominator to nodes in the cfg
      std::stack<node_indext> work;
      work.push(root);
      while(!work.empty())
      {
        node_indext v = work.top();
        work.pop();
        if(cfg_dominators.cfg[v - 1].dominators.empty())
        {
          cfg_dominators.cfg[v - 1].dominators =
            target_sett(dominators_data, v - 1);
          for_each_successor(v, [&](node_indext w) { work.push(w); });
        }
      }
    }

    /// Perform action on each child node
    template <typename Action>
    void for_each_successor(node_indext node_index, Action action)
    {
      // The -1 / +1 adjusts indices from 1 based to 0 based and back
      auto ix = node_index - 1;
      for(auto const &next :
          post_dom ? cfg_dominators.cfg.in(ix) : cfg_dominators.cfg.out(ix))
      {
        action(next.first + 1);
      }
    }

    /// Perform action on each parent node
    template <typename Action>
    void for_each_predecessor(node_indext node_index, Action action)
    {
      auto ix = node_index - 1;
      for(auto const &prev :
          post_dom ? cfg_dominators.cfg.out(ix) : cfg_dominators.cfg.in(ix))
      {
        action(prev.first + 1);
      }
    }
  };
};

/// Dominator tree computation
/// Follows "A fast algorithm for finding dominators in a flow graph" of
/// Lengauer and Tarjan. Node indices are 1-based as in the paper, with the
/// first element (with index 0) of each data structure simply left empty.
template <class P, class T, bool post_dom>
void cfg_dominators_templatet<P, T, post_dom>::fixedpointt::fixedpoint(
  P &program)
{
  // The nodes in the cfg data structure are represented by indices >= 0 and <
  // cfg.size(), whereas the internal data structures of the algorithm use
  // 1-based indices to represent nodes
  if(cfg_dominators.cfg.nodes_empty(program))
  {
    return;
  }
  cfg_dominators.entry_node = get_entry_node(program);
  node_indext root =
    cfg_dominators.cfg.entry_map[cfg_dominators.entry_node] + 1;

  // The computation is carried out in four steps as given in the paper.

  // Step 1
  // Number nodes in the order in which they are reached during DFS, and
  // initialize data structures
  dfs_counter = 0;
  dfs(root);

  for(node_indext i = dfs_counter; i >= 2; --i)
  {
    // Step 2
    // Compute semidominators
    node_indext w = vertex[i];
    // NOLINTNEXTLINE
    for_each_predecessor(w, [&](node_indext v) {
      node_indext u = eval(v);
      // Reachable nodes may have unreachable nodes as their parents
      if(semi[u] != 0 && semi[u] < semi[w])
      {
        semi[w] = semi[u];
      }
    });

    bucket[vertex[semi[w]]].insert(w);
    link(parent[w], w);

    // Step 3
    // Implicitely define immediate dominator
    auto &w_parent_bucket = bucket[parent[w]];
    for(auto v_it = begin(w_parent_bucket); v_it != end(w_parent_bucket);)
    {
      node_indext v = *v_it;
      v_it = w_parent_bucket.erase(v_it);
      node_indext u = eval(v);
      if(semi[u] < semi[v])
      {
        dom[v] = u;
      }
      else
      {
        dom[v] = parent[w];
      }
    }
  }

  // Step 4
  // Compute immediate dominator
  for(node_indext i = 2; i <= dfs_counter; ++i)
  {
    node_indext w = vertex[i];
    if(dom[w] != vertex[semi[w]])
    {
      dom[w] = dom[dom[w]];
    }
  }

  // Fill output data structures
  assign_dominators(root);
}

/// Print the result of the dominator computation
/// \param out: output stream
/// \param cfg_dominators: structure containing the result of the dominator
///   computation
template <class P, class T, bool post_dom>
std::ostream &operator<<(
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
  fixedpointt fixedpoint(*this);
  fixedpoint.fixedpoint(program);
}

/// Initialises the elements of the fixed point analysis
template <class P, class T, bool post_dom>
void cfg_dominators_templatet<P, T, post_dom>::initialise(P &program)
{
  cfg(program);
}

/// Pretty-print a single node. Supply a specialisation if operator<< is not
/// sufficient.
/// \param node: node to print
/// \param out: output stream
template <class T>
void dominators_pretty_print_node(const T &node, std::ostream &out)
{
  out << node;
}

/// Pretty-print a single node.
/// \param target: node to print
/// \param out: output stream
template <>
inline void dominators_pretty_print_node(
  const goto_programt::targett& target,
  std::ostream& out)
{
  out << target->code.pretty();
}


/// Print the result of the dominator computation
/// \param out: output stream
template <class P, class T, bool post_dom>
void cfg_dominators_templatet<P, T, post_dom>::output(std::ostream &out) const
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
          const goto_programt, goto_programt::const_targett, false>
        cfg_dominatorst;

typedef cfg_dominators_templatet<
          const goto_programt, goto_programt::const_targett, true>
        cfg_post_dominatorst;

/// Pretty-print a single node.
/// \param node: node to print
/// \param out: output stream
template <>
inline void dominators_pretty_print_node(
  const goto_programt::const_targett& node,
  std::ostream& out)
{
  out << node->location_number;
}

#endif // CPROVER_ANALYSES_CFG_DOMINATORS_H
