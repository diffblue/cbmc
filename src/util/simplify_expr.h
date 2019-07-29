/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_SIMPLIFY_EXPR_H
#define CPROVER_UTIL_SIMPLIFY_EXPR_H

class array_exprt;
class exprt;
class namespacet;
class refined_string_exprt;

#include <util/optional.h>

//
// simplify an expression
//
// true: did nothing
// false: simplified something
//

bool simplify(
  exprt &expr,
  const namespacet &ns);

// this is the preferred interface
exprt simplify_expr(exprt src, const namespacet &ns);

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
optionalt<std::reference_wrapper<const array_exprt>>
try_get_string_data_array(const exprt &content, const namespacet &ns);

#endif // CPROVER_UTIL_SIMPLIFY_EXPR_H
