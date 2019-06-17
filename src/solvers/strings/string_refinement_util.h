/*******************************************************************\

Module: String solver

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_UTIL_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_UTIL_H

#include <memory>

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
/// \param ns: namespace
/// \return true if a subtype of `type` is an pointer of characters.
///   The meaning of "subtype" is in the algebraic datatype sense: for example,
///   the subtypes of a struct are the types of its components, the subtype of
///   a pointer is the type it points to, etc...
bool has_char_pointer_subtype(const typet &type, const namespacet &ns);

/// \param expr: an expression
/// \param ns: namespace
/// \return true if a subexpression of `expr` is an array of characters
bool has_char_array_subexpr(const exprt &expr, const namespacet &ns);

/// Construct a string from a constant array.
/// \param arr: an array expression containing only constants
/// \param length: an unsigned value representing the length of the array
/// \return String of length `length` represented by the array assuming each
///   field in `arr` represents a character.
std::string
utf16_constant_array_to_java(const array_exprt &arr, std::size_t length);

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
  static exprt to_if_expression(const with_exprt &expr, const exprt &index);

protected:
  exprt default_value;
  std::map<std::size_t, exprt> entries;
  explicit sparse_arrayt(exprt default_value) : default_value(default_value)
  {
  }
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
  explicit interval_sparse_arrayt(const with_exprt &expr) : sparse_arrayt(expr)
  {
  }

  /// Initialize an array expression to sparse array representation, avoiding
  /// repetition of identical successive values and setting the default to
  /// `extra_value`.
  interval_sparse_arrayt(const array_exprt &expr, const exprt &extra_value);

  /// Initialize a sparse array from an array represented by a list of
  /// index-value pairs, and setting the default to `extra_value`.
  /// Indexes must be constant expressions, and negative indexes are ignored.
  interval_sparse_arrayt(
    const array_list_exprt &expr,
    const exprt &extra_value);

  exprt to_if_expression(const exprt &index) const;

  /// If the expression is an array_exprt or a with_exprt uses the appropriate
  /// constructor, otherwise returns empty optional.
  static optionalt<interval_sparse_arrayt>
  of_expr(const exprt &expr, const exprt &extra_value);

  /// Convert to an array representation, ignores elements at index >= size
  array_exprt concretize(std::size_t size, const typet &index_type) const;

  /// Get the value at the specified index.
  /// Complexity is logarithmic in the number of entries.
  exprt at(std::size_t index) const;

  /// Array containing the same value at each index.
  explicit interval_sparse_arrayt(exprt default_value)
    : sparse_arrayt(default_value)
  {
  }
};

#endif // CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_UTIL_H
