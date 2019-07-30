/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Expression skeleton

#include "expr_skeleton.h"

#include <util/std_expr.h>

expr_skeletont::expr_skeletont() : skeleton(nil_exprt{})
{
}

expr_skeletont expr_skeletont::remove_op0(exprt e)
{
  PRECONDITION(e.id() != ID_symbol);
  PRECONDITION(e.operands().size() >= 1);
  to_multi_ary_expr(e).op0().make_nil();
  return expr_skeletont{std::move(e)};
}

exprt expr_skeletont::apply(exprt expr) const
{
  PRECONDITION(skeleton.id() != ID_symbol);
  exprt result = skeleton;
  exprt *p = &result;

  while(p->is_not_nil())
  {
    INVARIANT(
      p->id() != ID_symbol,
      "expected pointed-to expression not to be a symbol");
    INVARIANT(
      p->operands().size() >= 1,
      "expected pointed-to expression to have at least one operand");
    p = &to_multi_ary_expr(*p).op0();
  }

  INVARIANT(p->is_nil(), "expected pointed-to expression to be nil");

  *p = std::move(expr);
  return result;
}

expr_skeletont expr_skeletont::compose(expr_skeletont other) const
{
  return expr_skeletont(apply(other.skeleton));
}
