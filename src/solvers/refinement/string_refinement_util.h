/*******************************************************************\

 Module: String solver

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_UTIL_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_UTIL_H

#include "string_constraint.h"

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
  // Record index of the equations that contain a given expression
  std::map<exprt, std::vector<std::size_t>> equations_containing;
  // Record expressions that are contained in the equation with the given index
  std::unordered_map<std::size_t, std::vector<exprt>> strings_in_equation;

  void add(const std::size_t i, const exprt &expr)
  {
    equations_containing[expr].push_back(i);
    strings_in_equation[i].push_back(expr);
  }

  std::vector<exprt> find_expressions(const std::size_t i)
  {
    return strings_in_equation[i];
  }

  std::vector<std::size_t> find_equations(const exprt &expr)
  {
    return equations_containing[expr];
  }
};

#endif // CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_UTIL_H
