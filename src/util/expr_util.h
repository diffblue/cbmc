/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

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
class symbolt;
class typet;
class namespacet;

/*! \deprecated This function will eventually be removed. Use functions from
 * \ref util/std_expr.h instead.
*/
exprt gen_zero(const typet &type);
/*! \copydoc gen_zero(const typet &) */
exprt gen_one(const typet &type);
/*! \copydoc gen_zero(const typet &) */
exprt gen_not_old(const exprt &op);

/*! \copydoc gen_zero(const typet &) */
void gen_and_old(exprt &expr);
/*! \copydoc gen_zero(const typet &) */
void gen_or_old(exprt &expr);

/*! \copydoc gen_zero(const typet &) */
void make_next_state(exprt &);

/*! \copydoc splits an expression with >=3 operands into nested binary expressions */
exprt make_binary(const exprt &);

/*! converts an udpate expr into a (possibly nested) with expression */
with_exprt make_with_expr(const update_exprt &);

/*! converts a scalar/float expression to C/C++ Booleans */
exprt is_not_zero(const exprt &, const namespacet &ns);

/*! negate a Boolean expression, possibly removing a not_exprt,
    and swapping false and true */
exprt boolean_negate(const exprt &);
