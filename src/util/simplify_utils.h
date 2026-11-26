/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_SIMPLIFY_UTILS_H
#define CPROVER_UTIL_SIMPLIFY_UTILS_H

#include "expr.h"

#include <string>

class array_exprt;
class constant_exprt;
class namespacet;

bool sort_operands(exprt::operandst &operands);

bool join_operands(exprt &expr);

bool sort_and_join(exprt &expr);

// bit-level conversions
std::optional<exprt> bits2expr(
  const std::string &bits,
  const typet &type,
  bool little_endian,
  const namespacet &ns);

std::optional<std::string>
expr2bits(const exprt &, bool little_endian, const namespacet &ns);

/// Determine whether \p constant is a pointer constant that holds an integer
/// address, i.e., whose value is the bit-vector representation of that
/// address. This excludes NULL as well as the symbolic values that the
/// back-ends use for pointer constants, such as "INVALID", "INVALID-<n>" or
/// ID_invalid.
/// \param constant: constant expression of any type
/// \return true iff \p constant has pointer type and a hexadecimal value
bool is_integer_address_constant(const constant_exprt &constant);

/// Get char sequence from content field of a refined string expression
///
/// If `content` is of the form `&id[e]`, where `id` is an array-typed symbol
/// expression (and `e` is any expression), return the value of the symbol `id`
/// (as given by the `value` field of the symbol in the namespace `ns`);
/// otherwise return an empty optional.
///
/// \param content: content field of a refined string expression
/// \param ns: namespace
/// \return array expression representing the char sequence which forms the
///   content of the refined string expression, empty optional if the content
///   cannot be determined
std::optional<std::reference_wrapper<const array_exprt>>
try_get_string_data_array(const exprt &content, const namespacet &ns);

#endif // CPROVER_UTIL_SIMPLIFY_UTILS_H
