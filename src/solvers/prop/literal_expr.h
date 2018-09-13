/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_PROP_LITERAL_EXPR_H
#define CPROVER_SOLVERS_PROP_LITERAL_EXPR_H

#include <util/std_expr.h>

#include "literal.h"

class literal_exprt:public predicate_exprt
{
public:
  explicit literal_exprt(literalt a):
    predicate_exprt(ID_literal)
  {
    set_literal(a);
  }

  literalt get_literal() const
  {
    literalt result;
    result.set(literalt::var_not(get_long_long(ID_literal)));
    return result;
  }

  void set_literal(literalt a)
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
inline const literal_exprt &to_literal_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_literal);
  DATA_INVARIANT(
    !expr.has_operands(), "literal expression should not have operands");
  return static_cast<const literal_exprt &>(expr);
}

/*! \copydoc to_literal_expr(const exprt &)
 * \ingroup gr_std_expr
*/
inline literal_exprt &to_literal_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_literal);
  DATA_INVARIANT(
    !expr.has_operands(), "literal expression should not have operands");
  return static_cast<literal_exprt &>(expr);
}

#endif // CPROVER_SOLVERS_PROP_LITERAL_EXPR_H
