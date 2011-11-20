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
class pointer_typet;
class symbol_exprt;
class symbolt;
class typet;

/*! \deprecated This function will eventually be removed. Use functions from
 * \ref util/std_expr.h instead.
*/
exprt gen_zero(const typet &type);
/*! \copydoc gen_zero(const typet &) */
exprt gen_one(const typet &type);
/*! \copydoc gen_zero(const typet &) */
exprt gen_not(const exprt &op);
/*! \copydoc gen_zero(const typet &) */
exprt gen_unary(const irep_idt &id, const typet &type, const exprt &op);
/*! \copydoc gen_zero(const typet &) */
exprt gen_binary(const irep_idt &id, const typet &type, const exprt &op1, const exprt &op2);
/*! \copydoc gen_zero(const typet &) */
exprt gen_and(const exprt &op1, const exprt &op2);
/*! \copydoc gen_zero(const typet &) */
exprt gen_and(const exprt &op1, const exprt &op2, const exprt &op3);
/*! \copydoc gen_zero(const typet &) */
exprt gen_or(const exprt &op1, const exprt &op2);
/*! \copydoc gen_zero(const typet &) */
exprt gen_or(const exprt &op1, const exprt &op2, const exprt &op3);
/*! \copydoc gen_zero(const typet &) */
exprt gen_implies(const exprt &op1, const exprt &op2);
/*! \copydoc gen_zero(const typet &) */
exprt gen_address_of(const exprt &op);

/*! \copydoc gen_zero(const typet &) */
pointer_typet gen_pointer_type(const typet &subtype);

/*! \copydoc gen_zero(const typet &) */
void gen_and(exprt &expr);
/*! \copydoc gen_zero(const typet &) */
void gen_or(exprt &expr);

/*! \copydoc gen_zero(const typet &) */
symbol_exprt symbol_expr(const symbolt &symbol);

/*! \copydoc gen_zero(const typet &) */
void make_next_state(exprt &expr);

/*! \copydoc gen_zero(const typet &) */
exprt make_binary(const exprt &src);
