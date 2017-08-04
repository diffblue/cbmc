/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_EXPR_UTIL_H
#define CPROVER_UTIL_EXPR_UTIL_H

/*! \file util/expr_util.h
 * \brief Deprecated expression utility functions
 *
 * \author Daniel Kroening <kroening@kroening.com>
 * \date   Sun Jul 31 21:54:44 BST 2011
*/

#include "irep.h"

class exprt;
class symbol_exprt;
class update_exprt;
class with_exprt;
class if_exprt;
class symbolt;
class typet;
class namespacet;

/// \deprecated This function will eventually be removed. Use functions
/// from \ref util/std_expr.h instead.

void make_next_state(exprt &);

/// splits an expression with >=3 operands into nested binary expressions
exprt make_binary(const exprt &);

/// converts an update expr into a (possibly nested) with expression
with_exprt make_with_expr(const update_exprt &);

/// converts a scalar/float expression to C/C++ Booleans
exprt is_not_zero(const exprt &, const namespacet &ns);

/// negate a Boolean expression, possibly removing a not_exprt,
/// and swapping false and true
exprt boolean_negate(const exprt &);

/// returns true if the expression has a subexpression with given ID
bool has_subexpr(const exprt &, const irep_idt &);

/// lift up an if_exprt one level
if_exprt lift_if(const exprt &, std::size_t operand_number);

#endif // CPROVER_UTIL_EXPR_UTIL_H
