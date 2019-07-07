/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr_class.h"

#include <cassert>

#include "arith_tools.h"
#include "c_types.h"
#include "config.h"
#include "expr_util.h"
#include "namespace.h"
#include "pointer_offset_size.h"
#include "pointer_predicates.h"
#include "prefix.h"
#include "std_expr.h"
#include "string_constant.h"
#include "threeval.h"

static bool is_dereference_integer_object(
  const exprt &expr,
  mp_integer &address)
{
  if(expr.id()==ID_dereference &&
     expr.operands().size()==1)
  {
    if(
      expr.op0().id() == ID_typecast && expr.op0().operands().size() == 1 &&
      expr.op0().op0().is_constant() &&
      !to_integer(to_constant_expr(expr.op0().op0()), address))
      return true;

    if(expr.op0().is_constant())
    {
      const constant_exprt &op0 = to_constant_expr(expr.op0());

      if(op0.get_value() == ID_NULL && config.ansi_c.NULL_is_zero) // NULL
      {
        address=0;
        return true;
      }
      else if(!to_integer(op0, address))
        return true;
    }
  }

  return false;
}

simplify_exprt::resultt<>
simplify_exprt::simplify_address_of_arg(const exprt &expr)
{
  if(expr.id()==ID_index)
  {
    auto new_index_expr = to_index_expr(expr);

    bool no_change = true;

    auto array_result = simplify_address_of_arg(new_index_expr.array());

    if(array_result.has_changed())
    {
      no_change = false;
      new_index_expr.array() = array_result.expr;
    }

    auto index_result = simplify_rec(new_index_expr.index());

    if(index_result.has_changed())
    {
      no_change = false;
      new_index_expr.index() = index_result.expr;
    }

    // rewrite (*(type *)int) [index] by
    // pushing the index inside

    mp_integer address;
    if(is_dereference_integer_object(new_index_expr.array(), address))
    {
      // push index into address
      auto step_size = pointer_offset_size(new_index_expr.type(), ns);

      if(step_size.has_value())
      {
        const auto index = numeric_cast<mp_integer>(new_index_expr.index());

        if(index.has_value())
        {
          pointer_typet pointer_type = to_pointer_type(
            to_dereference_expr(new_index_expr.array()).pointer().type());
          pointer_type.subtype() = new_index_expr.type();

          typecast_exprt typecast_expr(
            from_integer((*step_size) * (*index) + address, index_type()),
            pointer_type);

          return dereference_exprt{typecast_expr};
        }
      }
    }

    if(!no_change)
      return new_index_expr;
  }
  else if(expr.id()==ID_member)
  {
    auto new_member_expr = to_member_expr(expr);

    bool no_change = true;

    auto struct_op_result =
      simplify_address_of_arg(new_member_expr.struct_op());

    if(struct_op_result.has_changed())
    {
      new_member_expr.struct_op() = struct_op_result.expr;
      no_change = false;
    }

    const typet &op_type = ns.follow(new_member_expr.struct_op().type());

    if(op_type.id() == ID_struct)
    {
      // rewrite NULL -> member by
      // pushing the member inside

      mp_integer address;
      if(is_dereference_integer_object(new_member_expr.struct_op(), address))
      {
        const irep_idt &member = to_member_expr(expr).get_component_name();
        auto offset = member_offset(to_struct_type(op_type), member, ns);
        if(offset.has_value())
        {
          pointer_typet pointer_type = to_pointer_type(
            to_dereference_expr(new_member_expr.struct_op()).pointer().type());
          pointer_type.subtype() = new_member_expr.type();
          typecast_exprt typecast_expr(
            from_integer(address + *offset, index_type()), pointer_type);
          return dereference_exprt{typecast_expr};
        }
      }
    }

    if(!no_change)
      return new_member_expr;
  }
  else if(expr.id()==ID_dereference)
  {
    auto new_expr = to_dereference_expr(expr);
    auto r_pointer = simplify_rec(new_expr.pointer());
    if(r_pointer.has_changed())
    {
      new_expr.pointer() = r_pointer.expr;
      return std::move(new_expr);
    }
  }
  else if(expr.id()==ID_if)
  {
    auto new_if_expr = to_if_expr(expr);

    bool no_change = true;

    auto r_cond = simplify_rec(new_if_expr.cond());
    if(r_cond.has_changed())
    {
      new_if_expr.cond() = r_cond.expr;
      no_change = false;
    }

    auto true_result = simplify_address_of_arg(new_if_expr.true_case());
    if(true_result.has_changed())
    {
      new_if_expr.true_case() = true_result.expr;
      no_change = false;
    }

    auto false_result = simplify_address_of_arg(new_if_expr.false_case());

    if(false_result.has_changed())
    {
      new_if_expr.false_case() = false_result.expr;
      no_change = false;
    }

    // condition is a constant?
    if(new_if_expr.cond().is_true())
    {
      return new_if_expr.true_case();
    }
    else if(new_if_expr.cond().is_false())
    {
      return new_if_expr.false_case();
    }

    if(!no_change)
      return new_if_expr;
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_address_of(const address_of_exprt &expr)
{
  if(expr.type().id() != ID_pointer)
    return unchanged(expr);

  auto new_object = simplify_address_of_arg(expr.object());

  if(new_object.expr.id() == ID_index)
  {
    auto index_expr = to_index_expr(new_object.expr);

    if(!index_expr.index().is_zero())
    {
      // we normalize &a[i] to (&a[0])+i
      exprt offset = index_expr.op1();
      index_expr.op1()=from_integer(0, offset.type());
      auto new_address_of_expr = expr;
      new_address_of_expr.object() = std::move(index_expr);
      return plus_exprt(std::move(new_address_of_expr), offset);
    }
  }
  else if(new_object.expr.id() == ID_dereference)
  {
    // simplify &*p to p
    return to_dereference_expr(new_object.expr).pointer();
  }

  if(new_object.has_changed())
  {
    auto new_expr = expr;
    new_expr.object() = new_object;
    return new_expr;
  }
  else
    return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_pointer_offset(const unary_exprt &expr)
{
  const exprt &ptr = expr.op();

  if(ptr.id()==ID_if && ptr.operands().size()==3)
  {
    if_exprt if_expr=lift_if(expr, 0);
    if_expr.true_case() =
      simplify_pointer_offset(to_unary_expr(if_expr.true_case()));
    if_expr.false_case() =
      simplify_pointer_offset(to_unary_expr(if_expr.false_case()));
    return changed(simplify_if(if_expr));
  }

  if(ptr.type().id()!=ID_pointer)
    return unchanged(expr);

  if(ptr.id()==ID_address_of)
  {
    if(ptr.operands().size()!=1)
      return unchanged(expr);

    auto offset = compute_pointer_offset(ptr.op0(), ns);

    if(offset.has_value())
      return from_integer(*offset, expr.type());
  }
  else if(ptr.id()==ID_typecast) // pointer typecast
  {
    if(ptr.operands().size()!=1)
      return unchanged(expr);

    const typet &op_type = ptr.op0().type();

    if(op_type.id()==ID_pointer)
    {
      // Cast from pointer to pointer.
      // This just passes through, remove typecast.
      auto new_expr = expr;
      new_expr.op() = ptr.op0();

      simplify_node(new_expr); // recursive call
      return new_expr;
    }
    else if(op_type.id()==ID_signedbv ||
            op_type.id()==ID_unsignedbv)
    {
      // Cast from integer to pointer, say (int *)x.

      if(ptr.op0().is_constant())
      {
        // (T *)0x1234 -> 0x1234
        exprt tmp = typecast_exprt(ptr.op0(), expr.type());
        simplify_node(tmp);
        return tmp;
      }
      else
      {
        // We do a bit of special treatment for (TYPE *)(a+(int)&o),
        // which is re-written to 'a'.

        typet type = expr.type();
        exprt tmp=ptr.op0();
        if(tmp.id()==ID_plus && tmp.operands().size()==2)
        {
          if(tmp.op0().id()==ID_typecast &&
             tmp.op0().operands().size()==1 &&
             tmp.op0().op0().id()==ID_address_of)
          {
            auto new_expr = typecast_exprt::conditional_cast(tmp.op1(), type);

            simplify_node(new_expr);
            return new_expr;
          }
          else if(tmp.op1().id()==ID_typecast &&
                  tmp.op1().operands().size()==1 &&
                  tmp.op1().op0().id()==ID_address_of)
          {
            auto new_expr = typecast_exprt::conditional_cast(tmp.op0(), type);

            simplify_node(new_expr);
            return new_expr;
          }
        }
      }
    }
  }
  else if(ptr.id()==ID_plus) // pointer arithmetic
  {
    exprt::operandst ptr_expr;
    exprt::operandst int_expr;

    for(const auto &op : ptr.operands())
    {
      if(op.type().id()==ID_pointer)
        ptr_expr.push_back(op);
      else if(!op.is_zero())
      {
        exprt tmp=op;
        if(tmp.type()!=expr.type())
        {
          tmp = typecast_exprt(tmp, expr.type());
          simplify_node(tmp);
        }

        int_expr.push_back(tmp);
      }
    }

    if(ptr_expr.size()!=1 || int_expr.empty())
      return unchanged(expr);

    typet pointer_sub_type=ptr_expr.front().type().subtype();
    if(pointer_sub_type.id()==ID_empty)
      pointer_sub_type=char_type();

    auto element_size = pointer_offset_size(pointer_sub_type, ns);

    if(!element_size.has_value())
      return unchanged(expr);

    // this might change the type of the pointer!
    exprt pointer_offset_expr=pointer_offset(ptr_expr.front());
    simplify_node(pointer_offset_expr);

    exprt sum;

    if(int_expr.size()==1)
      sum=int_expr.front();
    else
    {
      sum=exprt(ID_plus, expr.type());
      sum.operands()=int_expr;
    }

    simplify_node(sum);

    exprt size_expr = from_integer(*element_size, expr.type());

    binary_exprt product(sum, ID_mult, size_expr, expr.type());

    simplify_node(product);

    auto new_expr =
      binary_exprt(pointer_offset_expr, ID_plus, product, expr.type());

    simplify_node(new_expr);

    return new_expr;
  }
  else if(ptr.id()==ID_constant)
  {
    const constant_exprt &c_ptr = to_constant_expr(ptr);

    if(c_ptr.get_value()==ID_NULL ||
       c_ptr.value_is_zero_string())
    {
      auto new_expr = from_integer(0, expr.type());

      simplify_node(new_expr);

      return new_expr;
    }
    else
    {
      // this is a pointer, we can't use to_integer
      const auto width = to_pointer_type(ptr.type()).get_width();
      mp_integer number = bvrep2integer(c_ptr.get_value(), width, false);
      // a null pointer would have been caught above, return value 0
      // will indicate that conversion failed
      if(number==0)
        return unchanged(expr);

      // The constant address consists of OBJECT-ID || OFFSET.
      mp_integer offset_bits =
        *pointer_offset_bits(ptr.type(), ns) - config.bv_encoding.object_bits;
      number%=power(2, offset_bits);

      auto new_expr = from_integer(number, expr.type());

      simplify_node(new_expr);

      return new_expr;
    }
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_inequality_address_of(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_equal || expr.id() == ID_notequal);
  PRECONDITION(expr.type().id() == ID_bool);
  DATA_INVARIANT(
    expr.operands().size() == 2, "(in)equalities have two operands");

  exprt tmp0=expr.op0();
  if(tmp0.id()==ID_typecast)
    tmp0=expr.op0().op0();
  if(tmp0.op0().id()==ID_index &&
     to_index_expr(tmp0.op0()).index().is_zero())
    tmp0=address_of_exprt(to_index_expr(tmp0.op0()).array());
  exprt tmp1=expr.op1();
  if(tmp1.id()==ID_typecast)
    tmp1=expr.op1().op0();
  if(tmp1.op0().id()==ID_index &&
     to_index_expr(tmp1.op0()).index().is_zero())
    tmp1=address_of_exprt(to_index_expr(tmp1.op0()).array());
  INVARIANT(tmp0.id() == ID_address_of, "id must be ID_address_of");
  INVARIANT(tmp1.id() == ID_address_of, "id must be ID_address_of");

  if(tmp0.operands().size()!=1)
    return unchanged(expr);
  if(tmp1.operands().size()!=1)
    return unchanged(expr);

  if(tmp0.op0().id()==ID_symbol &&
     tmp1.op0().id()==ID_symbol)
  {
    bool equal = to_symbol_expr(tmp0.op0()).get_identifier() ==
                 to_symbol_expr(tmp1.op0()).get_identifier();

    return make_boolean_expr(expr.id() == ID_equal ? equal : !equal);
  }
  else if(
    tmp0.op0().id() == ID_dynamic_object &&
    tmp1.op0().id() == ID_dynamic_object)
  {
    bool equal = to_dynamic_object_expr(tmp0.op0()).get_instance() ==
                 to_dynamic_object_expr(tmp1.op0()).get_instance();

    return make_boolean_expr(expr.id() == ID_equal ? equal : !equal);
  }
  else if(
    (tmp0.op0().id() == ID_symbol && tmp1.op0().id() == ID_dynamic_object) ||
    (tmp0.op0().id() == ID_dynamic_object && tmp1.op0().id() == ID_symbol))
  {
    return make_boolean_expr(expr.id() != ID_equal);
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_inequality_pointer_object(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_equal || expr.id() == ID_notequal);
  PRECONDITION(expr.type().id() == ID_bool);
  DATA_INVARIANT(
    expr.operands().size() == 2, "(in)equalities have two operands");

  exprt::operandst new_inequality_ops;
  forall_operands(it, expr)
  {
    PRECONDITION(it->id() == ID_pointer_object);
    PRECONDITION(it->operands().size() == 1);
    const exprt &op=it->op0();

    if(op.id()==ID_address_of)
    {
      if(
        op.operands().size() != 1 ||
        (op.op0().id() != ID_symbol && op.op0().id() != ID_dynamic_object &&
         op.op0().id() != ID_string_constant))
      {
        return unchanged(expr);
      }
    }
    else if(op.id() != ID_constant || !op.is_zero())
    {
      return unchanged(expr);
    }

    if(new_inequality_ops.empty())
      new_inequality_ops.push_back(op);
    else
    {
      new_inequality_ops.push_back(typecast_exprt::conditional_cast(
        op, new_inequality_ops.front().type()));
      simplify_node(new_inequality_ops.back());
    }
  }

  auto new_expr = expr;

  new_expr.operands() = std::move(new_inequality_ops);

  return changed(simplify_inequality(new_expr));
}

simplify_exprt::resultt<>
simplify_exprt::simplify_pointer_object(const unary_exprt &expr)
{
  const exprt &op = expr.op();

  auto op_result = simplify_object(op);

  if(op_result.expr.id() == ID_if)
  {
    const if_exprt &if_expr = to_if_expr(op_result.expr);
    exprt cond=if_expr.cond();

    exprt p_o_false=expr;
    p_o_false.op0()=if_expr.false_case();

    exprt p_o_true = expr;
    p_o_true.op0() = if_expr.true_case();

    auto new_expr = if_exprt(cond, p_o_true, p_o_false, expr.type());
    return changed(simplify_rec(new_expr));
  }

  if(op_result.has_changed())
  {
    auto new_expr = expr;
    new_expr.op() = op_result;
    return std::move(new_expr);
  }
  else
    return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_is_dynamic_object(const exprt &expr)
{
  // This should hold as a no_change of the expr ID being is_dynamic_object.
  PRECONDITION(expr.operands().size() == 1);

  auto new_expr = expr;
  exprt &op = new_expr.op0();

  if(op.id()==ID_if && op.operands().size()==3)
  {
    if_exprt if_expr=lift_if(expr, 0);
    if_expr.true_case() = simplify_is_dynamic_object(if_expr.true_case());
    if_expr.false_case() = simplify_is_dynamic_object(if_expr.false_case());
    return changed(simplify_if(if_expr));
  }

  bool no_change = true;

  auto op_result = simplify_object(op);

  if(op_result.has_changed())
  {
    op = op_result.expr;
    no_change = false;
  }

  // NULL is not dynamic
  if(op.id() == ID_constant && op.get(ID_value) == ID_NULL)
    return false_exprt();

  // &something depends on the something
  if(op.id()==ID_address_of && op.operands().size()==1)
  {
    if(op.op0().id()==ID_symbol)
    {
      const irep_idt identifier=to_symbol_expr(op.op0()).get_identifier();

      // this is for the benefit of symex
      return make_boolean_expr(
        has_prefix(id2string(identifier), SYMEX_DYNAMIC_PREFIX));
    }
    else if(op.op0().id()==ID_string_constant)
    {
      return false_exprt();
    }
    else if(op.op0().id()==ID_array)
    {
      return false_exprt();
    }
  }

  if(no_change)
    return unchanged(expr);
  else
    return std::move(new_expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_is_invalid_pointer(const exprt &expr)
{
  if(expr.operands().size()!=1)
    return unchanged(expr);

  auto new_expr = expr;
  exprt &op = new_expr.op0();
  bool no_change = true;

  auto op_result = simplify_object(op);

  if(op_result.has_changed())
  {
    op = op_result.expr;
    no_change = false;
  }

  // NULL is not invalid
  if(op.id()==ID_constant && op.get(ID_value)==ID_NULL)
  {
    return false_exprt();
  }

  // &anything is not invalid
  if(op.id()==ID_address_of)
  {
    return false_exprt();
  }

  if(no_change)
    return unchanged(expr);
  else
    return std::move(new_expr);
}

tvt simplify_exprt::objects_equal(const exprt &a, const exprt &b)
{
  if(a==b)
    return tvt(true);

  if(a.id()==ID_address_of && b.id()==ID_address_of &&
     a.operands().size()==1 && b.operands().size()==1)
    return objects_equal_address_of(a.op0(), b.op0());

  if(a.id()==ID_constant && b.id()==ID_constant &&
     a.get(ID_value)==ID_NULL && b.get(ID_value)==ID_NULL)
    return tvt(true);

  if(a.id()==ID_constant && b.id()==ID_address_of &&
     a.get(ID_value)==ID_NULL)
    return tvt(false);

  if(b.id()==ID_constant && a.id()==ID_address_of &&
     b.get(ID_value)==ID_NULL)
    return tvt(false);

  return tvt::unknown();
}

tvt simplify_exprt::objects_equal_address_of(const exprt &a, const exprt &b)
{
  if(a==b)
    return tvt(true);

  if(a.id()==ID_symbol && b.id()==ID_symbol)
  {
    if(to_symbol_expr(a).get_identifier() == to_symbol_expr(b).get_identifier())
      return tvt(true);
  }
  else if(a.id()==ID_index && b.id()==ID_index)
  {
    if(a.operands().size()==2 && b.operands().size()==2)
      return objects_equal_address_of(a.op0(), b.op0());
  }
  else if(a.id()==ID_member && b.id()==ID_member)
  {
    if(a.operands().size()==1 && b.operands().size()==1)
      return objects_equal_address_of(a.op0(), b.op0());
  }

  return tvt::unknown();
}

simplify_exprt::resultt<>
simplify_exprt::simplify_object_size(const unary_exprt &expr)
{
  auto new_expr = expr;
  bool no_change = true;
  exprt &op = new_expr.op();
  auto op_result = simplify_object(op);

  if(op_result.has_changed())
  {
    op = op_result.expr;
    no_change = false;
  }

  if(op.id()==ID_address_of && op.operands().size()==1)
  {
    if(op.op0().id()==ID_symbol)
    {
      // just get the type
      auto size_opt = size_of_expr(op.op0().type(), ns);

      if(size_opt.has_value())
      {
        const typet &expr_type = expr.type();
        exprt size = size_opt.value();

        if(size.type() != expr_type)
        {
          size = typecast_exprt(size, expr_type);
          simplify_node(size);
        }

        return size;
      }
    }
    else if(op.op0().id()==ID_string_constant)
    {
      typet type=expr.type();
      return from_integer(
        to_string_constant(op.op0()).get_value().size() + 1, type);
    }
  }

  if(no_change)
    return unchanged(expr);
  else
    return std::move(new_expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_good_pointer(const unary_exprt &expr)
{
  // we expand the definition
  exprt def = good_pointer_def(expr.op(), ns);

  // recursive call
  simplify_node(def);

  return std::move(def);
}
