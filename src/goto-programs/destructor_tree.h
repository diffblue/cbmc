/*******************************************************************\

 Module: Destructor Tree

 Author: John Dumbell, john.dumbell@diffblue.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_DESTRUCTOR_TREE_H
#define CPROVER_GOTO_PROGRAMS_DESTRUCTOR_TREE_H

#include <util/graph.h>
#include <util/std_code.h>

typedef std::size_t node_indext;

/// Result of an attempt to find ancestor information about two nodes. Holds
/// the information about who the common ancestor node is as well as depth of
/// the two nodes relative to the common ancestor
class ancestry_resultt
{
public:
  explicit ancestry_resultt(node_indext node)
    : common_ancestor(node),
      left_depth_below_common_ancestor(0),
      right_depth_below_common_ancestor(0)
  {
  }
  ancestry_resultt(
    node_indext node,
    std::size_t left_pre_size,
    std::size_t right_pre_size)
    : common_ancestor(node),
      left_depth_below_common_ancestor(left_pre_size),
      right_depth_below_common_ancestor(right_pre_size)
  {
  }
  node_indext common_ancestor;
  std::size_t left_depth_below_common_ancestor;
  std::size_t right_depth_below_common_ancestor;
};

/// Result of a tree query holding both destructor codet and the ID of the node
/// that held it.
class destructor_and_idt
{
public:
  destructor_and_idt(const codet &code, node_indext id)
    : destructor(code), node_id(id)
  {
  }

  const codet destructor;
  node_indext node_id;
};

/// Tree to keep track of the destructors generated along each branch of a
/// function. Used to compare and find out what dead
/// instructions are needed when moving from one branch to another.
///
/// For example, if you had this code:
///
/// object a;
/// if (enabled)
///   object b;
///   object c;
/// else
///   object e;
///
/// It would generate a tree like this:
///
///           -> b -> c
/// Root -> a
///           -> e
///
/// Where each split represents a different block and each letter represents
/// the destructor codet for that particular variable.
///
/// To find out anything interesting you need to get a node ID (currently only
/// got by calling get_current_node at a particular point in the tree) and then
/// use that later to compare against a different point in the tree.
///
/// So if I took note of the nodes at the end of each branch (c, e) and wanted
/// to compare them, I'd find that 'a' is the common ancestor, and the steps
/// required to get there from 'c' was 2 and 'e' was 1, which also tells
/// you if a certain branch is a prefix or not. In this case neither are a
/// prefix of the other.
class destructor_treet
{
public:
  destructor_treet()
  {
    // We add a default node to the graph to act as a root for path traversal.
    this->destruction_graph.add_node();
  }

  /// Adds a destructor to the current stack, attaching itself to the
  /// current node.
  void add(const codet &destructor);

  /// Fetches the destructor value for the passed-in node index.
  optionalt<codet> &get_destructor(node_indext index);

  /// Builds a vector of destructors that start from starting_index and ends
  /// at end_index.
  /// \param end_index Index of the first variable to keep.
  ///     List won't include this node. If empty, root of the current stack.
  /// \param starting_index Index of the first variable to destroy. If empty,
  ///     top of the current stack.
  /// \return collection of destructors that should be called for the
  ///     range supplied.
  const std::vector<destructor_and_idt> get_destructors(
    optionalt<node_indext> end_index = {},
    optionalt<node_indext> starting_index = {});

  /// Finds the nearest common ancestor of two nodes and then returns it.
  /// This should be used when you want to find out what parts of the two
  /// branches are common to each other.
  const ancestry_resultt get_nearest_common_ancestor_info(
    node_indext left_index,
    node_indext right_index);

  /// Sets the current node. Next time a node is added to the stack it will
  /// be added as a child of this node. If passed an empty index, no
  /// assignment will be done.
  void set_current_node(optionalt<node_indext> val);

  /// Sets the current node. Next time a node is added to the stack it will
  /// be added as a child of this node.
  void set_current_node(node_indext val);

  /// Gets the node that the next addition will be added to as a child.
  node_indext get_current_node() const;

  /// Walks the current node down to its child.
  void descend_tree();

private:
  class destructor_nodet : public graph_nodet<empty_edget>
  {
  public:
    destructor_nodet() = default;

    explicit destructor_nodet(codet destructor)
      : destructor_value(std::move(destructor))
    {
    }
    optionalt<codet> destructor_value;
  };

  grapht<destructor_nodet> destruction_graph;
  node_indext current_node = 0;
};

#endif // CPROVER_GOTO_PROGRAMS_DESTRUCTOR_TREE_H
