/*******************************************************************\

 Module: String solver

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_UTIL_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_UTIL_H

#include "string_constraint.h"

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

#endif // CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_UTIL_H
