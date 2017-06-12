/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "expr_util.h"
#include "expr.h"
#include "fixedbv.h"
#include "ieee_float.h"
#include "std_expr.h"
#include "symbol.h"
#include "namespace.h"
#include "arith_tools.h"

void make_next_state(exprt &expr)
{
  Forall_operands(it, expr)
    make_next_state(*it);

  if(expr.id()==ID_symbol)
    expr.id(ID_next_symbol);
}

exprt make_binary(const exprt &expr)
{
  const exprt::operandst &operands=expr.operands();

  if(operands.size()<=2)
    return expr;

  // types must be identical for make_binary to be safe to use
  const typet &type=expr.type();

  exprt previous=operands.front();
  assert(previous.type()==type);

  for(exprt::operandst::const_iterator
      it=++operands.begin();
      it!=operands.end();
      ++it)
  {
    assert(it->type()==type);

    exprt tmp=expr;
    tmp.operands().clear();
    tmp.operands().resize(2);
    tmp.op0().swap(previous);
    tmp.op1()=*it;
    previous.swap(tmp);
  }

  return previous;
}

with_exprt make_with_expr(const update_exprt &src)
{
  const exprt::operandst &designator=src.designator();
  assert(!designator.empty());

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
      assert(false);

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
  assert(zero.is_not_nil());

  binary_exprt comparison(src, id, zero, bool_typet());
  comparison.add_source_location()=src.source_location();

  return comparison;
}

exprt boolean_negate(const exprt &src)
{
  if(src.id()==ID_not && src.operands().size()==1)
    return src.op0();
  else if(src.is_true())
    return false_exprt();
  else if(src.is_false())
    return true_exprt();
  else
    return not_exprt(src);
}

bool has_subexpr(const exprt &src, const irep_idt &id)
{
  if(src.id()==id)
    return true;

  forall_operands(it, src)
    if(has_subexpr(*it, id))
      return true;

  return false;
}

if_exprt lift_if(const exprt &src, std::size_t operand_number)
{
  assert(operand_number<src.operands().size());
  assert(src.operands()[operand_number].id()==ID_if);

  const if_exprt if_expr=to_if_expr(src.operands()[operand_number]);
  const exprt true_case=if_expr.true_case();
  const exprt false_case=if_expr.false_case();

  if_exprt result;
  result.cond()=if_expr.cond();
  result.type()=src.type();
  result.true_case()=src;
  result.true_case().operands()[operand_number]=true_case;
  result.false_case()=src;
  result.false_case().operands()[operand_number]=false_case;

  return result;
}
