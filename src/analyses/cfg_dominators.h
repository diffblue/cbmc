/*******************************************************************\

Module: Compute dominators for CFG of goto_function

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

/// \file
/// Compute dominators for CFG of goto_function

#ifndef CPROVER_ANALYSES_CFG_DOMINATORS_H
#define CPROVER_ANALYSES_CFG_DOMINATORS_H

#include <cassert>
#include <iosfwd>
#include <iterator>
#include <list>
#include <map>
#include <set>

#include <goto-programs/cfg.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_program.h>

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
  struct nodet
  {
    optionalt<std::size_t> dominator;
    // Not on the stack; not seen yet
    static const int NODE_NOT_VISITED = -1;
    // On the stack but not yet numbered
    static const int NODE_INDEX_PENDING = -2;
    int postorder_index = NODE_NOT_VISITED;
  };

  typedef procedure_local_cfg_baset<nodet, P, T> cfgt;
  cfgt cfg;
  using cfg_nodet = typename cfgt::nodet;

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

  /// Iterator that allows you to walk lazily up dominators from an entry node.
  class dominators_iterablet
  {
    // Type of our containing \ref dense_integer_mapt
    using cfg_dominatorst = cfg_dominators_templatet<P, T, post_dom>;

  public:
    class dominators_iteratort
      : public std::iterator<std::forward_iterator_tag, T>
    {
      // Type of the std::iterator support class we inherit
      using base_typet = std::iterator<std::forward_iterator_tag, const T>;

    public:
      dominators_iteratort(
        const cfg_dominatorst &dominator_analysis,
        std::size_t index)
        : dominator_analysis(dominator_analysis), current_index(index)
      {
      }

    private:
      explicit dominators_iteratort(const cfg_dominatorst &dominator_analysis)
        : dominator_analysis(dominator_analysis), current_index{}
      {
      }

    public:
      static dominators_iteratort end(const cfg_dominatorst &dominator_analysis)
      {
        return dominators_iteratort{dominator_analysis};
      }

      dominators_iteratort operator++()
      {
        auto i = *this;
        advance();
        return i;
      }
      dominators_iteratort operator++(int junk)
      {
        advance();
        return *this;
      }
      const cfg_nodet &get_node() const
      {
        return dominator_analysis.cfg[*current_index];
      }
      typename base_typet::reference operator*() const
      {
        return get_node().PC;
      }
      typename base_typet::pointer operator->() const
      {
        return &**this;
      }
      bool operator==(const dominators_iteratort &rhs) const
      {
        return current_index == rhs.current_index;
      }
      bool operator!=(const dominators_iteratort &rhs) const
      {
        return current_index != rhs.current_index;
      }

    private:
      void advance()
      {
        INVARIANT(current_index.has_value(), "can't advance an end() iterator");
        const auto &current_node = dominator_analysis.cfg[*current_index];
        const auto &next_dominator = current_node.dominator;
        INVARIANT(
          current_node.postorder_index ==
              cfg_dominatorst::nodet::NODE_NOT_VISITED ||
            next_dominator.has_value(),
          "reachable nodes' dominator chains should lead to the root");

        if(!next_dominator || *next_dominator == *current_index)
        {
          // Cycle; this is the root node
          current_index = optionalt<std::size_t>{};
        }
        else
        {
          current_index = next_dominator;
        }
      }

      const cfg_dominatorst &dominator_analysis;
      optionalt<std::size_t> current_index;
    };

    dominators_iterablet(
      const cfg_dominatorst &dominator_analysis,
      optionalt<std::size_t> index)
      : dominator_analysis(dominator_analysis), first_instruction_index(index)
    {
    }

    dominators_iteratort begin() const
    {
      if(first_instruction_index.has_value())
        return dominators_iteratort{dominator_analysis,
                                    *first_instruction_index};
      else
        return dominators_iteratort::end(dominator_analysis);
    }

    dominators_iteratort end() const
    {
      return dominators_iteratort::end(dominator_analysis);
    }

  private:
    const cfg_dominatorst &dominator_analysis;
    optionalt<std::size_t> first_instruction_index;
  };

  template <class U>
  dominators_iterablet dominators(U start_instruction) const
  {
    return dominators_iterablet{*this, cfg.get_node_index(start_instruction)};
  }

  /// Returns true if program point \p lhs dominates \p rhs.
  /// Note by definition all program points dominate themselves.
  bool dominates(T lhs, T rhs) const
  {
    const auto rhs_dominators = dominators(rhs);
    return std::any_of(
      rhs_dominators.begin(), rhs_dominators.end(), [&lhs](const T dominator) {
        return lhs == dominator;
      });
  }

  /// Returns true if program point \p lhs dominates the instruction
  /// corresponding to \p rhs_node.
  /// Note by definition all program points dominate themselves.
  bool dominates(T lhs, const typename cfgt::nodet &rhs_node) const
  {
    return dominates(lhs, rhs_node.PC);
  }

  /// Returns true if the program point for \p program_point_node is reachable
  /// from the entry point. Saves a lookup compared to the overload taking a
  /// program point, so use this overload if you already have the node.
  bool program_point_reachable(const nodet &program_point_node) const
  {
    // Dominator analysis walks from the entry point, so a side-effect is to
    // identify unreachable program points (those which don't dominate even
    // themselves).
    return program_point_node.dominator.has_value();
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

  /// Assigns post-order numbering to each node in the tree.
  /// Full explanation here: https://en.wikipedia.org/wiki/Tree_traversal.
  void assign_postordering(std::size_t start_node_index);

  /// Sort our CFG nodes in reverse post-order. Just gets every node that we've
  /// processed (anything not NODE_NOT_VISITED) then orders from highest to
  /// lowest. This excludes the entry-node though.
  std::vector<T>
  get_reverse_postordered_instructions(std::size_t entry_node_index) const;

  /// Walks up the dominators of left/right nodes until it finds one that is
  /// common to both sides. Used to work out the nearest common dominator
  /// when a node that has multiple incoming edges.
  ///
  /// Noted by figure 3 in "A Simple, Fast Dominance Algorithm" by Cooper,
  /// Harvey and Kennedy.
  const cfg_nodet &intersect(
    const cfg_nodet &left_input_node,
    const cfg_nodet &right_input_node);
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

template <class P, class T, bool post_dom>
void cfg_dominators_templatet<P, T, post_dom>::assign_postordering(
  std::size_t start_node_index)
{
  struct stack_entryt
  {
    // cfg index, not the post-order index we're assigning
    std::size_t node_index;
    typename cfgt::nodet::edgest::const_iterator child_iterator;
    typename cfgt::nodet::edgest::const_iterator child_end;
  };

  std::size_t next_postorder_index = 0;
  std::vector<stack_entryt> stack;

  auto place_node_on_stack_if_not_visited = [this,
                                             &stack](std::size_t node_index) {
    // If we've already visited this node, don't re-calculate.
    auto &node = cfg[node_index];
    if(node.postorder_index != nodet::NODE_NOT_VISITED)
      return;

    // Otherwise set that we've processed it, and put the node on the stack.
    const auto &node_successors = post_dom ? node.in : node.out;
    stack.push_back(
      {node_index, node_successors.begin(), node_successors.end()});
    node.postorder_index = nodet::NODE_INDEX_PENDING;
  };

  place_node_on_stack_if_not_visited(start_node_index);
  INVARIANT(stack.size() == 1, "entry node should not be visited yet");

  /// Do the actual post-order processing.
  while(!stack.empty())
  {
    auto &stack_top = stack.back();
    auto &current_node = cfg[stack_top.node_index];

    INVARIANT(
      current_node.postorder_index == nodet::NODE_INDEX_PENDING,
      "a node on the stack should not be numbered yet");

    // If we've already numbered all of our children, number ourselves
    // and remove the node from further processing.
    if(stack_top.child_iterator == stack_top.child_end)
    {
      // Node children all visited; number this node
      current_node.postorder_index = next_postorder_index++;
      stack.pop_back();
    }
    else
    {
      // Otherwise put children on the stack to be visited.
      // Alter top of stack before it is perhaps reallocated on extension:
      const auto next_child_index = stack_top.child_iterator->first;
      ++stack_top.child_iterator;
      place_node_on_stack_if_not_visited(next_child_index);
    }
  }
}

template <class P, class T, bool post_dom>
std::vector<T>
cfg_dominators_templatet<P, T, post_dom>::get_reverse_postordered_instructions(
  std::size_t entry_node_index) const
{
  auto reverse_postordering = [this](T lhs, T rhs) {
    return cfg.get_node(lhs).postorder_index >
           cfg.get_node(rhs).postorder_index;
  };

  std::vector<T> order;

  // Note that this will only select and order nodes that are reachable from
  // the entry point.
  for(std::size_t i = 0; i < cfg.size(); ++i)
  {
    if(
      i != entry_node_index &&
      cfg[i].postorder_index != nodet::NODE_NOT_VISITED)
    {
      order.push_back(cfg[i].PC);
    }
  }

  std::sort(order.begin(), order.end(), reverse_postordering);

  return order;
}

/// Computes the MOP for the dominator analysis
template <class P, class T, bool post_dom>
void cfg_dominators_templatet<P, T, post_dom>::fixedpoint(P &program)
{
  if(cfgt::nodes_empty(program))
    return;

  // Initialise entry node to be its own dominator:
  if(post_dom)
    entry_node = cfgt::get_last_node(program);
  else
    entry_node = cfgt::get_first_node(program);
  typename cfgt::nodet &n = cfg.get_node(entry_node);
  const auto entry_node_index = cfg.get_node_index(entry_node);
  n.dominator = entry_node_index;

  // Calculate a post-ordering on the CFG:
  assign_postordering(entry_node_index);

  const auto visit_order =
    get_reverse_postordered_instructions(entry_node_index);

  bool any_change = true;

  while(any_change)
  {
    any_change = false;
    for(const auto current : visit_order)
    {
      auto &node = cfg.get_node(current);
      const cfg_nodet *dominator_node = nullptr;

      // compute intersection of predecessors
      for(const auto &edge : (post_dom ? node.out : node.in))
      {
        const typename cfgt::nodet &other = cfg[edge.first];
        if(!other.dominator)
          continue;

        if(!dominator_node)
          dominator_node = &other;
        else
          dominator_node = &intersect(*dominator_node, other);
      }

      // If the calculated dominator is different than the one already
      // existing on the node, or hasn't got an existing dominator, update and
      // then re-calculate dominators.
      if(
        dominator_node != nullptr &&
        (!node.dominator || dominator_node->postorder_index !=
                              cfg[*node.dominator].postorder_index))
      {
        node.dominator = cfg.get_node_index(dominator_node->PC);
        // Note when any node's immediate dominator changes this way we re-visit
        // the *whole* graph again in post-order, because changing one node's
        // immediate dominator may change the dominator *set* of an instruction
        // some distance away.

        // We could optimise this to only re-visit instructions reachable from
        // the change site.
        any_change = true;
      }
    }
  }
}

template <class P, class T, bool post_dom>
const typename cfg_dominators_templatet<P, T, post_dom>::cfgt::nodet &
cfg_dominators_templatet<P, T, post_dom>::intersect(
  const cfg_nodet &left_input_node,
  const cfg_nodet &right_input_node)
{
  auto left_node_dominators = dominators(left_input_node.PC);
  auto right_node_dominators = dominators(right_input_node.PC);
  auto left_it = left_node_dominators.begin();
  auto right_it = right_node_dominators.begin();

  while(left_it.get_node().postorder_index !=
        right_it.get_node().postorder_index)
  {
    while(left_it.get_node().postorder_index <
          right_it.get_node().postorder_index)
    {
      ++left_it;
      INVARIANT(
        left_it != left_node_dominators.end(),
        "should only move the iterator that is further from the root");
    }

    while(right_it.get_node().postorder_index <
          left_it.get_node().postorder_index)
    {
      ++right_it;
      INVARIANT(
        right_it != right_node_dominators.end(),
        "should only move the iterator that is further from the root");
    }
  }

  return left_it.get_node();
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
  for(const auto &node : cfg.entries())
  {
    auto n=node.first;

    dominators_pretty_print_node(n, out);
    if(post_dom)
      out << " post-dominated by ";
    else
      out << " dominated by ";
    bool first=true;
    for(auto &d : dominators(n))
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
