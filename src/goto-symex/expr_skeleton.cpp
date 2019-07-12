/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Expression skeleton

#include "expr_skeleton.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/mp_arith.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

expr_skeletont::expr_skeletont(typet missing_type)
  : skeleton(nil_exprt{}), type_of_missing_part(std::move(missing_type))
{
}

expr_skeletont expr_skeletont::remove_op0(exprt e)
{
  PRECONDITION(e.id() != ID_symbol);
  PRECONDITION(e.operands().size() >= 1);
  typet missing = std::move(e.op0().type());
  e.op0().make_nil();
  return expr_skeletont{std::move(e), std::move(missing)};
}

exprt expr_skeletont::apply(exprt expr) const
{
  PRECONDITION(skeleton.id() != ID_symbol);
  PRECONDITION(expr.type() == type_of_missing_part);
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
  typet missing_type = other.type_of_missing_part;
  return expr_skeletont{apply(std::move(other.skeleton)),
                        std::move(missing_type)};
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
    typet new_missing_type = index_expr->type();
    index_expr->make_nil();
    return expr_skeletont{std::move(skeleton.skeleton),
                          std::move(new_missing_type)};
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
    typet new_missing_type = member->type();
    member->make_nil();
    return expr_skeletont{std::move(skeleton.skeleton),
                          std::move(new_missing_type)};
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
  typet new_missing_type = to_update->type();
  to_update->make_nil();
  return expr_skeletont{std::move(skeleton.skeleton),
                        std::move(new_missing_type)};
}

expr_skeletont expr_skeletont::revert_byte_extract_aux(
  expr_skeletont skeleton,
  exprt offset,
  const typet &type,
  const namespacet &ns,
  exprt offset_already_removed)
{
  offset = simplify_expr(std::move(offset), ns);
  const exprt offset_reached =
    simplify_expr(equal_exprt{offset_already_removed, offset}, ns);
  if(offset_reached.is_true() && type == skeleton.type_of_missing_part)
    return expr_skeletont{std::move(skeleton)};
  const exprt offset_exceeded = simplify_expr(
    binary_relation_exprt{offset_already_removed, ID_gt, offset}, ns);
  exprt *deepest = deepest_not_nil(skeleton.skeleton);
  if(deepest == nullptr || offset_exceeded.is_true())
  {
    // In case of empty skeleton or if the offset has been exceeded, compose
    // with `byte_extract(☐, offset_already_removed - offset)`
    const minus_exprt offset_diff{std::move(offset_already_removed), offset};
    const auto simplified = simplify_expr(offset_diff, ns);
    return skeleton.compose(expr_skeletont{
      byte_extract_exprt{byte_extract_id(), nil_exprt{}, simplified, type},
      skeleton.type_of_missing_part});
  }
  const auto offset_resulting_from_deepest_operation = [&]() -> exprt {
    if(auto byte_extract = expr_try_dynamic_cast<byte_extract_exprt>(*deepest))
      return byte_extract->offset();
    if(auto index_expr = expr_try_dynamic_cast<index_exprt>(*deepest))
    {
      auto element_size_in_bits = pointer_offset_bits(index_expr->type(), ns);
      CHECK_RETURN(element_size_in_bits);
      mult_exprt offset_in_bits{
        index_expr->index(),
        from_integer(*element_size_in_bits, index_expr->index().type())};
      return div_exprt{offset_in_bits, from_integer(8, offset_in_bits.type())};
    }
    auto member_expr = expr_try_dynamic_cast<member_exprt>(*deepest);
    INVARIANT(
      member_expr,
      "Skeleton should only be composed of byte_extract, index and member "
      "exprts");
    auto struct_type =
      type_try_dynamic_cast<struct_typet>(skeleton.type_of_missing_part);
    INVARIANT(
      struct_type,
      "In member_exprt skeleton the missing part should have struct type");
    auto member_offset =
      member_offset_expr(*struct_type, member_expr->get_component_name(), ns);
    CHECK_RETURN(member_offset);
    return *member_offset;
  }();

  typet new_missing_type = deepest->type();
  deepest->make_nil();
  skeleton.type_of_missing_part = new_missing_type;
  return revert_byte_extract_aux(
    skeleton,
    offset,
    type,
    ns,
    plus_exprt{std::move(offset_already_removed),
               offset_resulting_from_deepest_operation});
}

expr_skeletont expr_skeletont::revert_byte_extract(
  expr_skeletont skeleton,
  exprt offset,
  const typet &type,
  const namespacet &ns)
{
  exprt init_already_removed = from_integer(0, offset.type());
  return revert_byte_extract_aux(
    std::move(skeleton),
    std::move(offset),
    type,
    ns,
    std::move(init_already_removed));
}
