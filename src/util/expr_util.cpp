/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "expr_util.h"

#include <algorithm>
#include <unordered_set>

#include "expr.h"
#include "expr_iterator.h"
#include "fixedbv.h"
#include "ieee_float.h"
#include "std_expr.h"
#include "symbol.h"
#include "namespace.h"
#include "arith_tools.h"

bool is_lvalue(const exprt &expr)
{
  if(expr.id() == ID_index)
    return is_lvalue(to_index_expr(expr).array());
  else if(expr.id() == ID_member)
    return is_lvalue(to_member_expr(expr).compound());
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

  with_exprt result;
  exprt *dest=&result;

  forall_expr(it, designator)
  {
    with_exprt tmp;

    if(it->id()==ID_index_designator)
    {
      tmp.where()=to_index_designator(*it).index();
    }
    else if(it->id()==ID_member_designator)
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

  const typet &src_type=
    src.type().id()==ID_c_enum_tag?
    ns.follow_tag(to_c_enum_tag_type(src.type())):
    ns.follow(src.type());

  if(src_type.id()==ID_bool) // already there
    return src; // do nothing

  irep_idt id=
    src_type.id()==ID_floatbv?ID_ieee_float_notequal:ID_notequal;

  exprt zero=from_integer(0, src_type);
  CHECK_RETURN(zero.is_not_nil());

  binary_exprt comparison(src, id, zero, bool_typet());
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
    else if(top.id() == ID_symbol)
      push_if_not_visited(ns.follow(top));
    else if(top.id() == ID_c_enum_tag)
      push_if_not_visited(ns.follow_tag(to_c_enum_tag_type(top)));
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
bool is_constantt::is_constant(const exprt &expr) const
{
  if(expr.is_constant())
    return true;

  if(expr.id() == ID_address_of)
  {
    return is_constant_address_of(to_address_of_expr(expr).object());
  }
  else if(
    expr.id() == ID_typecast || expr.id() == ID_array_of ||
    expr.id() == ID_plus || expr.id() == ID_mult || expr.id() == ID_array ||
    expr.id() == ID_with || expr.id() == ID_struct || expr.id() == ID_union ||
    // byte_update works, byte_extract may be out-of-bounds
    expr.id() == ID_byte_update_big_endian ||
    expr.id() == ID_byte_update_little_endian)
  {
    return std::all_of(
      expr.operands().begin(), expr.operands().end(), [this](const exprt &e) {
        return is_constant(e);
      });
  }

  return false;
}

/// this function determines which reference-typed expressions are constant
bool is_constantt::is_constant_address_of(const exprt &expr) const
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
