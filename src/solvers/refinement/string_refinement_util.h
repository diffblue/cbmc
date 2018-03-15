/*******************************************************************\

 Module: String solver

 Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_UTIL_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_UTIL_H

#include "string_builtin_function.h"
#include "string_constraint.h"
#include "string_constraint_generator.h"

/// For now, any unsigned bitvector type of width smaller or equal to 16 is
/// considered a character.
/// \note type that are not characters maybe detected as characters (for
/// instance unsigned char in C), this will make dec_solve do unnecessary
/// steps for these, but should not affect correctness.
/// \param type: a type
/// \return true if the given type represents characters
bool is_char_type(const typet &type);

/// Distinguish char array from other types.
/// For now, any unsigned bitvector type is considered a character.
/// \param type: a type
/// \param ns: namespace
/// \return true if the given type is an array of characters
bool is_char_array_type(const typet &type, const namespacet &ns);

/// For now, any unsigned bitvector type is considered a character.
/// \param type: a type
/// \return true if the given type represents a pointer to characters
bool is_char_pointer_type(const typet &type);

/// \param type: a type
/// \param pred: a predicate
/// \return true if one of the subtype of `type` satisfies predicate `pred`.
///         The meaning of "subtype" is in the algebraic datatype sense:
///         for example, the subtypes of a struct are the types of its
///         components, the subtype of a pointer is the type it points to,
///         etc...
///         For instance in the type `t` defined by
///         `{ int a; char[] b; double * c; { bool d} e}`, `int`, `char`,
///         `double` and `bool` are subtypes of `t`.
bool has_subtype(
  const typet &type,
  const std::function<bool(const typet &)> &pred);

/// \param type: a type
/// \return true if a subtype of `type` is an pointer of characters.
///         The meaning of "subtype" is in the algebraic datatype sense:
///         for example, the subtypes of a struct are the types of its
///         components, the subtype of a pointer is the type it points to,
///         etc...
bool has_char_pointer_subtype(const typet &type);

/// \param type: a type
/// \return true if a subtype of `type` is string_typet.
///         The meaning of "subtype" is in the algebraic datatype sense:
///         for example, the subtypes of a struct are the types of its
///         components, the subtype of a pointer is the type it points to,
///         etc...
bool has_string_subtype(const typet &type);

/// \param expr: an expression
/// \param ns: namespace
/// \return true if a subexpression of `expr` is an array of characters
bool has_char_array_subexpr(const exprt &expr, const namespacet &ns);

struct index_set_pairt
{
  std::map<exprt, std::set<exprt>> cumulative;
  std::map<exprt, std::set<exprt>> current;
};

struct string_axiomst
{
  std::vector<string_constraintt> universal;
  std::vector<string_not_contains_constraintt> not_contains;
};

/// Represents arrays of the form `array_of(x) with {i:=a} with {j:=b} ...`
/// by a default value `x` and a list of entries `(i,a)`, `(j,b)` etc.
class sparse_arrayt
{
public:
  /// Initialize a sparse array from an expression of the form
  /// `array_of(x) with {i:=a} with {j:=b} ...`
  /// This is the form in which array valuations coming from the underlying
  /// solver are given.
  explicit sparse_arrayt(const with_exprt &expr);

  /// Creates an if_expr corresponding to the result of accessing the array
  /// at the given index
  virtual exprt to_if_expression(const exprt &index) const;

protected:
  exprt default_value;
  std::vector<std::pair<std::size_t, exprt>> entries;
};

/// Represents arrays by the indexes up to which the value remains the same.
/// For instance `{'a', 'a', 'a', 'b', 'b', 'c'}` would be represented by
/// by ('a', 2) ; ('b', 4), ('c', 5).
/// This is particularly useful when the array is constant on intervals.
class interval_sparse_arrayt final : public sparse_arrayt
{
public:
  /// An expression of the form `array_of(x) with {i:=a} with {j:=b}` is
  /// converted to an array `arr` where for all index `k` smaller than `i`,
  /// `arr[k]` is `a`, for all index between `i` (exclusive) and `j` it is `b`
  /// and for the others it is `x`.
  explicit interval_sparse_arrayt(const with_exprt &expr);
  exprt to_if_expression(const exprt &index) const override;
};

/// Maps equation to expressions contained in them and conversely expressions to
/// equations that contain them. This can be used on a subset of expressions
/// which interests us, in particular strings. Equations are identified by an
/// index of type `std::size_t` for more efficient insertion and lookup.
class equation_symbol_mappingt
{
public:
  /// Record the fact that equation `i` contains expression `expr`
  void add(const std::size_t i, const exprt &expr);

  /// \param i: index corresponding to an equation
  /// \return vector of expressions contained in the equation with the given
  ///   index `i`
  std::vector<exprt> find_expressions(const std::size_t i);

  /// \param expr: an expression
  /// \return vector of equations containing the given expression `expr`
  std::vector<std::size_t> find_equations(const exprt &expr);

private:
  /// Record index of the equations that contain a given expression
  std::map<exprt, std::vector<std::size_t>> equations_containing;
  /// Record expressions that are contained in the equation with the given index
  std::unordered_map<std::size_t, std::vector<exprt>> strings_in_equation;
};


/// Keep track of dependencies between strings.
/// Each string points to the builtin_function calls on which it depends.
/// Each builtin_function points to the strings on which the result depends.
class string_dependenciest
{
public:
  /// A builtin_function node is just an index in the `builtin_function_nodes`
  /// vector.
  class builtin_function_nodet
  {
  public:
    std::size_t index;
    explicit builtin_function_nodet(std::size_t i) : index(i)
    {
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
    // builtin functions on which it depends
    std::vector<builtin_function_nodet> dependencies;
    // builtin function of which it is the result
    optionalt<builtin_function_nodet> result_from;
    // In case it depends on a builtin_function we don't support yet
    bool depends_on_unknown_builtin_function = false;

    explicit string_nodet(array_string_exprt e, const std::size_t index)
      : expr(std::move(e)), index(index)
    {
    }
  };

  string_nodet &get_node(const array_string_exprt &e);

  std::unique_ptr<const string_nodet>
  node_at(const array_string_exprt &e) const;

  /// `builtin_function` is reset to an empty pointer after the node is created
  builtin_function_nodet
  make_node(std::unique_ptr<string_builtin_functiont> &builtin_function);
  const std::vector<builtin_function_nodet> &
  dependencies(const string_nodet &node) const;
  const string_builtin_functiont &
  get_builtin_function(const builtin_function_nodet &node) const;

  /// Add edge from node for `e` to node for `builtin_function` if `e` is a
  /// simple array expression. If it is an `if_exprt` we add the sub-expressions
  /// that are not `if_exprt`s instead.
  void add_dependency(
    const array_string_exprt &e,
    const builtin_function_nodet &builtin_function);

  /// Mark node for `e` as depending on unknown builtin_function
  void add_unknown_dependency(const array_string_exprt &e);

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

private:
  /// Set of nodes representing builtin_functions
  std::vector<std::unique_ptr<string_builtin_functiont>> builtin_function_nodes;

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
  };

  mutable std::vector<optionalt<exprt>> eval_string_cache;

  /// Applies `f` on all nodes
  void for_each_node(const std::function<void(const nodet &)> &f) const;

  /// Applies `f` on all successors of the node n
  void for_each_successor(
    const nodet &i,
    const std::function<void(const nodet &)> &f) const;
};

/// When right hand side of equation is a builtin_function add
/// a "string_builtin_function" node to the graph and connect it to the strings
/// on which it depends and which depends on it.
/// If the string builtin_function is not a supported one, mark all the string
/// arguments as depending on an unknown builtin_function.
/// \param dependencies: graph to which we add the node
/// \param equation: an equation whose right hand side is possibly a call to a
///   string builtin_function.
/// \param array_pool: array pool containing arrays corresponding to the string
///   exprt arguments of the builtin_function call
/// \return true if a node was added, if false is returned it either means that
///   the right hand side is not a function application
/// \todo there should be a class with just the three functions we require here
bool add_node(
  string_dependenciest &dependencies,
  const equal_exprt &equation,
  array_poolt &array_pool);

#endif // CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_UTIL_H
