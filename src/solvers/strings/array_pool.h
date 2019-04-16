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

  exprt get_length(const array_string_exprt &s) const;

  void insert(const exprt &pointer_expr, array_string_exprt &array);

  const array_string_exprt &find(const exprt &pointer, const exprt &length);

  const std::set<array_string_exprt> &created_strings() const;

  array_string_exprt
  fresh_string(const typet &index_type, const typet &char_type);

private:
  // associate arrays to char pointers
  std::unordered_map<exprt, array_string_exprt, irep_hash> arrays_of_pointers;

  // associate length to arrays of infinite size
  std::unordered_map<array_string_exprt, symbol_exprt, irep_hash>
    length_of_array;

  // generates fresh symbols
  symbol_generatort &fresh_symbol;

  // Strings created in the pool
  std::set<array_string_exprt> created_strings_value;

  array_string_exprt make_char_array_for_char_pointer(
    const exprt &char_pointer,
    const typet &char_array_type);
};

/// Converts a struct containing a length and pointer to an array.
/// This allows to get a string expression from arguments of a string
/// builtion function, because string arguments in these function calls
/// are given as a struct containing a length and pointer to an array.
array_string_exprt of_argument(array_poolt &array_pool, const exprt &arg);

/// Return the array associated to the given pointer or creates a new one
DEPRECATED("use pool.find(pointer, length) instead")
const array_string_exprt &char_array_of_pointer(
  array_poolt &pool,
  const exprt &pointer,
  const exprt &length);

array_string_exprt get_string_expr(array_poolt &pool, const exprt &expr);

#endif // CPROVER_SOLVERS_STRINGS_ARRAY_POOL_H
