/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LITERAL_EXPR_H
#define CPROVER_LITERAL_EXPR_H

#include <util/std_expr.h>

#include "literal.h"

class literal_exprt:public predicate_exprt
{
public:
  inline explicit literal_exprt(literalt a):
    predicate_exprt(ID_literal)
  {
    set_literal(a);
  }

  inline literalt get_literal() const
  {
    literalt result;
    result.set(get_long_long(ID_literal));
    return result;
  }

  inline void set_literal(literalt a)
  {
    set(ID_literal, a.get());
  }
};

/*! \brief Cast a generic exprt to a \ref literal_exprt
 *
 * This is an unchecked conversion. \a expr must be known to be \ref
 * literal_exprt.
 *
 * \param expr Source expression
 * \return Object of type \ref literal_exprt
 *
 * \ingroup gr_std_expr
*/
extern inline const literal_exprt &to_literal_expr(const exprt &expr)
{
  assert(expr.id()==ID_literal && !expr.has_operands());
  return static_cast<const literal_exprt &>(expr);
}

/*! \copydoc to_literal_expr(const exprt &)
 * \ingroup gr_std_expr
*/
extern inline literal_exprt &to_literal_expr(exprt &expr)
{
  assert(expr.id()==ID_literal && !expr.has_operands());
  return static_cast<literal_exprt &>(expr);
}

#endif
