/*******************************************************************\

Module: String solver

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Associates arrays and length to pointers, so that the string refinement can
/// transform builtin function calls with pointer arguments to formulas over
/// arrays.

#ifndef CPROVER_SOLVERS_STRINGS_ARRAY_POOL_H
#define CPROVER_SOLVERS_STRINGS_ARRAY_POOL_H

#include <set>
#include <util/std_expr.h>
#include <util/string_expr.h>

/// Generation of fresh symbols of a given type
class symbol_generatort final
{
public:
  /// Generate a new symbol expression of the given \p type with some \p prefix
  /// \return a symbol of type \p type whose name starts with
  ///   "string_refinement#" followed by \p prefix
  symbol_exprt
  operator()(const irep_idt &prefix, const typet &type = bool_typet());

private:
  unsigned symbol_count = 0;

#ifdef DEBUG
public:
  /// Keep track of created symbols, for debugging purposes.
  std::vector<symbol_exprt> created_symbols;
#endif
};

/// Correspondance between arrays and pointers string representations
class array_poolt final
{
public:
  explicit array_poolt(symbol_generatort &symbol_generator)
    : fresh_symbol(symbol_generator)
  {
  }

  const std::unordered_map<exprt, array_string_exprt, irep_hash> &
  get_arrays_of_pointers() const
  {
    return arrays_of_pointers;
  }

  /// Get the length of an array_string_exprt from the array_pool. If the length
  /// does not yet exist, create a new symbol and add it to the pool.
  ///
  /// If the array_string_exprt is an `if` expression, the true and false parts
  /// are handled independently (and recursively). That is, no new length symbol
  /// is added to the pool for `if` expressions, but symbols may be added for
  /// each of the parts.
  /// \param s: array expression representing a string
  /// \return expression for the length of `s`
  exprt get_or_create_length(const array_string_exprt &s);

  /// As opposed to get_length(), do not create a new symbol if the length
  /// of the array_string_exprt does not have one in the array_pool, but instead
  /// return an empty optional.
  /// \param s: array expression representing a string
  /// \return expression for the length of `s`, or empty optional
  optionalt<exprt> get_length_if_exists(const array_string_exprt &s) const;

  void insert(const exprt &pointer_expr, const array_string_exprt &array);

  /// Creates a new array if the pointer is not pointing to an array
  array_string_exprt find(const exprt &pointer, const exprt &length);

  const std::unordered_map<array_string_exprt, exprt, irep_hash> &
  created_strings() const;

  /// Construct a string expression whose length and content are new variables
  /// \param index_type: type used to index characters of the strings
  /// \param char_type: type of characters
  /// \return a string expression
  array_string_exprt
  fresh_string(const typet &index_type, const typet &char_type);

private:
  /// Associate arrays to char pointers
  /// Invariant: Each array_string_exprt in this map has a corresponding entry
  ///            in length_of_array.
  ///            This is enforced whenever we add an element to
  ///            `arrays_of_pointers`, i.e. fresh_string()
  ///            and make_char_array_for_char_pointer().
  std::unordered_map<exprt, array_string_exprt, irep_hash> arrays_of_pointers;

  /// Associate length to arrays of infinite size
  std::unordered_map<array_string_exprt, exprt, irep_hash> length_of_array;

  /// Generate fresh symbols
  symbol_generatort &fresh_symbol;

  array_string_exprt make_char_array_for_char_pointer(
    const exprt &char_pointer,
    const typet &char_array_type);
};

/// Converts a struct containing a length and pointer to an array.
/// This allows to get a string expression from arguments of a string
/// builtion function, because string arguments in these function calls
/// are given as a struct containing a length and pointer to an array.
array_string_exprt of_argument(array_poolt &array_pool, const exprt &arg);

/// Fetch the string_exprt corresponding to the given refined_string_exprt
/// \param array_pool: pool of arrays representing strings
/// \param expr: an expression of refined string type
/// \return a string expression
array_string_exprt get_string_expr(array_poolt &array_pool, const exprt &expr);

#endif // CPROVER_SOLVERS_STRINGS_ARRAY_POOL_H
