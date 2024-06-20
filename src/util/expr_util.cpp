/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "expr_util.h"

#include "arith_tools.h"
#include "bitvector_expr.h"
#include "byte_operators.h"
#include "c_types.h"
#include "config.h"
#include "expr_iterator.h"
#include "namespace.h"
#include "pointer_expr.h"
#include "pointer_offset_size.h"

#include <algorithm>
#include <unordered_set>

bool is_assignable(const exprt &expr)
{
  if(expr.id() == ID_index)
    return is_assignable(to_index_expr(expr).array());
  else if(expr.id() == ID_member)
    return is_assignable(to_member_expr(expr).compound());
  else if(expr.id() == ID_dereference)
    return true;
  else if(expr.id() == ID_symbol)
    return true;
  else
    return false;
}

exprt make_binary(const exprt &expr)
{
  const exprt::operandst &operands=expr.operands();

  if(operands.size()<=2)
    return expr;

  // types must be identical for make_binary to be safe to use
  const typet &type=expr.type();

  exprt previous=operands.front();
  PRECONDITION(previous.type()==type);

  for(exprt::operandst::const_iterator
      it=++operands.begin();
      it!=operands.end();
      ++it)
  {
    PRECONDITION(it->type()==type);

    exprt tmp=expr;
    tmp.operands().clear();
    tmp.operands().resize(2);
    to_binary_expr(tmp).op0().swap(previous);
    to_binary_expr(tmp).op1() = *it;
    previous.swap(tmp);
  }

  return previous;
}

with_exprt make_with_expr(const update_exprt &src)
{
  const exprt::operandst &designator=src.designator();
  PRECONDITION(!designator.empty());

  with_exprt result{exprt{}, exprt{}, exprt{}};
  exprt *dest=&result;

  for(const auto &expr : designator)
  {
    with_exprt tmp{exprt{}, exprt{}, exprt{}};

    if(expr.id() == ID_index_designator)
    {
      tmp.where() = to_index_designator(expr).index();
    }
    else if(expr.id() == ID_member_designator)
    {
      // irep_idt component_name=
      //  to_member_designator(*it).get_component_name();
    }
    else
      UNREACHABLE;

    *dest=tmp;
    dest=&to_with_expr(*dest).new_value();
  }

  return result;
}

exprt is_not_zero(
  const exprt &src,
  const namespacet &ns)
{
  // We frequently need to check if a numerical type is not zero.
  // We replace (_Bool)x by x!=0; use ieee_float_notequal for floats.
  // Note that this returns a proper bool_typet(), not a C/C++ boolean.
  // To get a C/C++ boolean, add a further typecast.

  const typet &src_type = src.type().id() == ID_c_enum_tag
                            ? ns.follow_tag(to_c_enum_tag_type(src.type()))
                            : src.type();

  if(src_type.id()==ID_bool) // already there
    return src; // do nothing

  irep_idt id=
    src_type.id()==ID_floatbv?ID_ieee_float_notequal:ID_notequal;

  exprt zero=from_integer(0, src_type);
  // Use tag type if applicable:
  zero.type() = src.type();

  binary_relation_exprt comparison(src, id, std::move(zero));
  comparison.add_source_location()=src.source_location();

  return std::move(comparison);
}

exprt boolean_negate(const exprt &src)
{
  if(src.id() == ID_not)
    return to_not_expr(src).op();
  else if(src.is_true())
    return false_exprt();
  else if(src.is_false())
    return true_exprt();
  else
    return not_exprt(src);
}

bool has_subexpr(
  const exprt &expr,
  const std::function<bool(const exprt &)> &pred)
{
  const auto it = std::find_if(expr.depth_begin(), expr.depth_end(), pred);
  return it != expr.depth_end();
}

bool has_subexpr(const exprt &src, const irep_idt &id)
{
  return has_subexpr(
    src, [&](const exprt &subexpr) { return subexpr.id() == id; });
}

bool has_subtype(
  const typet &type,
  const std::function<bool(const typet &)> &pred,
  const namespacet &ns)
{
  std::vector<std::reference_wrapper<const typet>> stack;
  std::unordered_set<typet, irep_hash> visited;

  const auto push_if_not_visited = [&](const typet &t) {
    if(visited.insert(t).second)
      stack.emplace_back(t);
  };

  push_if_not_visited(type);
  while(!stack.empty())
  {
    const typet &top = stack.back().get();
    stack.pop_back();

    if(pred(top))
      return true;
    else if(top.id() == ID_c_enum_tag)
      push_if_not_visited(ns.follow_tag(to_c_enum_tag_type(top)));
    else if(top.id() == ID_struct_tag)
      push_if_not_visited(ns.follow_tag(to_struct_tag_type(top)));
    else if(top.id() == ID_union_tag)
      push_if_not_visited(ns.follow_tag(to_union_tag_type(top)));
    else if(top.id() == ID_struct || top.id() == ID_union)
    {
      for(const auto &comp : to_struct_union_type(top).components())
        push_if_not_visited(comp.type());
    }
    else
    {
      for(const auto &subtype : to_type_with_subtypes(top).subtypes())
        push_if_not_visited(subtype);
    }
  }

  return false;
}

bool has_subtype(const typet &type, const irep_idt &id, const namespacet &ns)
{
  return has_subtype(
    type, [&](const typet &subtype) { return subtype.id() == id; }, ns);
}

if_exprt lift_if(const exprt &src, std::size_t operand_number)
{
  PRECONDITION(operand_number<src.operands().size());
  PRECONDITION(src.operands()[operand_number].id()==ID_if);

  const if_exprt if_expr=to_if_expr(src.operands()[operand_number]);
  const exprt true_case=if_expr.true_case();
  const exprt false_case=if_expr.false_case();

  if_exprt result(if_expr.cond(), src, src);
  result.true_case().operands()[operand_number]=true_case;
  result.false_case().operands()[operand_number]=false_case;

  return result;
}

const exprt &skip_typecast(const exprt &expr)
{
  if(expr.id()!=ID_typecast)
    return expr;

  return skip_typecast(to_typecast_expr(expr).op());
}

/// This function determines what expressions are to be propagated as
/// "constants"
bool can_forward_propagatet::is_constant(const exprt &expr) const
{
  if(
    expr.id() == ID_symbol || expr.id() == ID_nondet_symbol ||
    expr.id() == ID_side_effect)
  {
    return false;
  }

  if(expr.id() == ID_address_of)
  {
    return is_constant_address_of(to_address_of_expr(expr).object());
  }
  else if(auto index = expr_try_dynamic_cast<index_exprt>(expr))
  {
    if(!is_constant(index->array()) || !index->index().is_constant())
      return false;

    const auto &array_type = to_array_type(index->array().type());
    if(!array_type.size().is_constant())
      return false;

    const mp_integer size =
      numeric_cast_v<mp_integer>(to_constant_expr(array_type.size()));
    const mp_integer index_int =
      numeric_cast_v<mp_integer>(to_constant_expr(index->index()));

    return index_int >= 0 && index_int < size;
  }
  else if(auto be = expr_try_dynamic_cast<byte_extract_exprt>(expr))
  {
    if(!is_constant(be->op()) || !be->offset().is_constant())
      return false;

    const auto op_bits = pointer_offset_bits(be->op().type(), ns);
    if(!op_bits.has_value())
      return false;

    const auto extract_bits = pointer_offset_bits(be->type(), ns);
    if(!extract_bits.has_value())
      return false;

    const bitst offset_bits{
      numeric_cast_v<mp_integer>(to_constant_expr(be->offset())) *
      be->get_bits_per_byte()};

    return offset_bits >= bitst{0} && offset_bits + *extract_bits <= *op_bits;
  }
  else if(auto eb = expr_try_dynamic_cast<extractbits_exprt>(expr))
  {
    if(!is_constant(eb->src()) || !eb->index().is_constant())
    {
      return false;
    }

    const auto eb_bits = pointer_offset_bits(eb->type(), ns);
    if(!eb_bits.has_value())
      return false;

    const auto src_bits = pointer_offset_bits(eb->src().type(), ns);
    if(!src_bits.has_value())
      return false;

    const bitst lower_bound =
      numeric_cast_v<bitst>(to_constant_expr(eb->index()));
    const bitst upper_bound = lower_bound + eb_bits.value() - bitst{1};

    return lower_bound >= bitst{0} && lower_bound <= upper_bound &&
           upper_bound < src_bits.value();
  }
  else
  {
    // std::all_of returns true when there are no operands
    return std::all_of(
      expr.operands().begin(), expr.operands().end(), [this](const exprt &e) {
        return is_constant(e);
      });
  }
}

/// this function determines which reference-typed expressions are constant
bool can_forward_propagatet::is_constant_address_of(const exprt &expr) const
{
  if(expr.id() == ID_symbol)
  {
    return true;
  }
  else if(expr.id() == ID_index)
  {
    const index_exprt &index_expr = to_index_expr(expr);

    return is_constant_address_of(index_expr.array()) &&
           is_constant(index_expr.index());
  }
  else if(expr.id() == ID_member)
  {
    return is_constant_address_of(to_member_expr(expr).compound());
  }
  else if(expr.id() == ID_dereference)
  {
    const dereference_exprt &deref = to_dereference_expr(expr);

    return is_constant(deref.pointer());
  }
  else if(expr.id() == ID_string_constant)
    return true;

  return false;
}

constant_exprt make_boolean_expr(bool value)
{
  if(value)
    return true_exprt();
  else
    return false_exprt();
}

exprt make_and(exprt a, exprt b)
{
  PRECONDITION(a.is_boolean() && b.is_boolean());
  if(b.is_constant())
  {
    if(b.get(ID_value) == ID_false)
      return false_exprt{};
    return a;
  }
  if(a.is_constant())
  {
    if(a.get(ID_value) == ID_false)
      return false_exprt{};
    return b;
  }
  if(b.id() == ID_and)
  {
    b.add_to_operands(std::move(a));
    return b;
  }
  return and_exprt{std::move(a), std::move(b)};
}

bool is_null_pointer(const constant_exprt &expr)
{
  if(expr.type().id() != ID_pointer)
    return false;

  if(expr.get_value() == ID_NULL)
    return true;

    // We used to support "0" (when NULL_is_zero), but really front-ends should
    // resolve this and generate ID_NULL instead.
#if 0
  return config.ansi_c.NULL_is_zero && expr.value_is_zero_string();
#else
  INVARIANT(
    !expr.value_is_zero_string() || !config.ansi_c.NULL_is_zero,
    "front-end should use ID_NULL");
  return false;
#endif
}
