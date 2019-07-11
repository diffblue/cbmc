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
  e.op0().make_nil();
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
    p = &p->op0();
  }

  INVARIANT(p->is_nil(), "expected pointed-to expression to be nil");

  *p = std::move(expr);
  return result;
}

expr_skeletont expr_skeletont::compose(expr_skeletont other) const
{
  return expr_skeletont(apply(other.skeleton));
}

/// In the expression corresponding to a skeleton returns a pointer to the
/// deepest subexpression before we encounter nil.
/// Returns nullptr if \p e is nil
static exprt *deepest_not_nil(exprt &e)
{
  if(e.is_nil())
    return nullptr;
  exprt *ptr = &e;
  while(!ptr->op0().is_nil())
    ptr = &ptr->op0();
  return ptr;
}

optionalt<expr_skeletont>
expr_skeletont::clear_innermost_index_expr(expr_skeletont skeleton)
{
  exprt *to_update = deepest_not_nil(skeleton.skeleton);
  if(to_update == nullptr)
    return {};
  if(index_exprt *index_expr = expr_try_dynamic_cast<index_exprt>(*to_update))
  {
    index_expr->make_nil();
    return expr_skeletont{std::move(skeleton)};
  }
  return {};
}

optionalt<expr_skeletont>
expr_skeletont::clear_innermost_member_expr(expr_skeletont skeleton)
{
  exprt *to_update = deepest_not_nil(skeleton.skeleton);
  if(to_update == nullptr)
    return {};
  if(member_exprt *member = expr_try_dynamic_cast<member_exprt>(*to_update))
  {
    member->make_nil();
    return expr_skeletont{std::move(skeleton)};
  }
  return {};
}

optionalt<expr_skeletont>
expr_skeletont::clear_innermost_byte_extract_expr(expr_skeletont skeleton)
{
  exprt *to_update = deepest_not_nil(skeleton.skeleton);
  if(to_update == nullptr)
    return {};
  if(
    to_update->id() != ID_byte_extract_big_endian &&
    to_update->id() != ID_byte_extract_little_endian)
  {
    return {};
  }
  to_update->make_nil();
  return expr_skeletont{std::move(skeleton.skeleton)};
}
