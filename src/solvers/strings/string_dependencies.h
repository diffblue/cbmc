/*******************************************************************\

Module: String solver

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Keeps track of dependencies between strings.

#ifndef CPROVER_SOLVERS_STRINGS_STRING_DEPENDENCIES_H
#define CPROVER_SOLVERS_STRINGS_STRING_DEPENDENCIES_H

#include <memory>

#include <util/nodiscard.h>

#include "string_builtin_function.h"

/// Keep track of dependencies between strings.
/// Each string points to the builtin_function calls on which it depends.
/// Each builtin_function points to the strings on which the result depends.
class string_dependenciest
{
public:
  /// A builtin function node contains a builtin function call
  class builtin_function_nodet
  {
  public:
    // index in the `builtin_function_nodes` vector
    std::size_t index;
    // pointer to the builtin function
    std::unique_ptr<string_builtin_functiont> data;

    explicit builtin_function_nodet(
      std::unique_ptr<string_builtin_functiont> d,
      std::size_t i)
      : index(i), data(std::move(d))
    {
    }

    builtin_function_nodet(builtin_function_nodet &&other)
      : index(other.index), data(std::move(other.data))
    {
    }

    builtin_function_nodet &operator=(builtin_function_nodet &&other)
    {
      index = other.index;
      data = std::move(other.data);
      return *this;
    }
  };

  /// A string node points to builtin_function on which it depends
  class string_nodet
  {
  public:
    // expression the node corresponds to
    array_string_exprt expr;
    // index in the string_nodes vector
    std::size_t index;
    // builtin functions on which it depends, refered by there index in
    // builtin_function node vector.
    // \todo should these we shared pointers?
    std::vector<std::size_t> dependencies;
    // builtin function of which it is the result
    optionalt<std::size_t> result_from;

    explicit string_nodet(array_string_exprt e, const std::size_t index)
      : expr(std::move(e)), index(index)
    {
    }
  };

  string_nodet &get_node(const array_string_exprt &e);

  std::unique_ptr<const string_nodet>
  node_at(const array_string_exprt &e) const;

  builtin_function_nodet &
  make_node(std::unique_ptr<string_builtin_functiont> builtin_function);
  const string_builtin_functiont &
  get_builtin_function(const builtin_function_nodet &node) const;

  /// Add edge from node for `e` to node for `builtin_function` if `e` is a
  /// simple array expression. If it is an `if_exprt` we add the sub-expressions
  /// that are not `if_exprt`s instead.
  void add_dependency(
    const array_string_exprt &e,
    const builtin_function_nodet &builtin_function);

  /// Applies `f` to each node on which `node` depends
  void for_each_dependency(
    const string_nodet &node,
    const std::function<void(const builtin_function_nodet &)> &f) const;
  void for_each_dependency(
    const builtin_function_nodet &node,
    const std::function<void(const string_nodet &)> &f) const;

  /// Attempt to evaluate the given string from the dependencies and valuation
  /// of strings on which it depends
  /// Warning: eval uses a cache which must be cleaned everytime the valuations
  /// given by get_value can change.
  optionalt<exprt> eval(
    const array_string_exprt &s,
    const std::function<exprt(const exprt &)> &get_value) const;

  /// Clean the cache used by `eval`
  void clean_cache();

  void output_dot(std::ostream &stream) const;

  /// For all builtin call on which a test (or an unsupported buitin)
  /// result depends, add the corresponding constraints. For the other builtin
  /// only add constraints on the length.
  NODISCARD string_constraintst
  add_constraints(string_constraint_generatort &generatort);

  /// Clear the content of the dependency graph
  void clear();

private:
  /// Set of nodes representing builtin_functions
  std::vector<builtin_function_nodet> builtin_function_nodes;

  /// Set of nodes representing strings
  std::vector<string_nodet> string_nodes;

  /// Nodes describing dependencies of a string: values of the map correspond
  /// to indexes in the vector `string_nodes`.
  std::unordered_map<array_string_exprt, std::size_t, irep_hash>
    node_index_pool;

  class nodet
  {
  public:
    enum
    {
      BUILTIN,
      STRING
    } kind;
    std::size_t index;

    explicit nodet(const builtin_function_nodet &builtin)
      : kind(BUILTIN), index(builtin.index)
    {
    }

    explicit nodet(const string_nodet &string_node)
      : kind(STRING), index(string_node.index)
    {
    }

    bool operator==(const nodet &n) const
    {
      return n.kind == kind && n.index == index;
    }
  };

  /// Hash function for nodes
  // NOLINTNEXTLINE(readability/identifiers)
  struct node_hash
  {
    size_t
    operator()(const string_dependenciest::nodet &node) const optional_noexcept
    {
      return 2 * node.index +
             (node.kind == string_dependenciest::nodet::STRING ? 0 : 1);
    }
  };

  mutable std::vector<optionalt<exprt>> eval_string_cache;

  /// Applies `f` on all nodes
  void for_each_node(const std::function<void(const nodet &)> &f) const;

  /// Applies `f` on all successors of the node n
  void for_each_successor(
    const nodet &i,
    const std::function<void(const nodet &)> &f) const;
};

/// When a sub-expression of \p expr is a builtin_function, add
/// a "string_builtin_function" node to the graph and connect it to the strings
/// on which it depends and which depends on it.
/// If the string builtin_function is not a supported one, mark all the string
/// arguments as depending on an unknown builtin_function.
/// \param dependencies: graph to which we add the node
/// \param expr: an expression which may contain a call to a
///   string builtin_function.
/// \param array_pool: array pool containing arrays corresponding to the string
///   exprt arguments of the builtin_function call
/// \param fresh_symbol: used to create new symbols for the return values of
///   builtin functions
/// \return An expression in which function applications have been replaced
///   by symbols corresponding to the `return_value` field of the associated
///   builtin function. Or an empty optional when no function applications has
///   been encountered
/// \todo there should be a class with just the three functions we require here
optionalt<exprt> add_node(
  string_dependenciest &dependencies,
  const exprt &expr,
  array_poolt &array_pool,
  symbol_generatort &fresh_symbol);

#endif // CPROVER_SOLVERS_STRINGS_STRING_DEPENDENCIES_H
