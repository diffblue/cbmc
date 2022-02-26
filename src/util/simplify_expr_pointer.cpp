/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr_class.h"

#include "arith_tools.h"
#include "c_types.h"
#include "config.h"
#include "expr_util.h"
#include "namespace.h"
#include "pointer_expr.h"
#include "pointer_offset_size.h"
#include "pointer_predicates.h"
#include "prefix.h"
#include "std_expr.h"
#include "string_constant.h"

static bool is_dereference_integer_object(
  const exprt &expr,
  mp_integer &address)
{
  if(expr.id() == ID_dereference)
  {
    const auto &pointer = to_dereference_expr(expr).pointer();

    if(
      pointer.id() == ID_typecast &&
      to_typecast_expr(pointer).op().is_constant() &&
      !to_integer(to_constant_expr(to_typecast_expr(pointer).op()), address))
    {
      return true;
    }

    if(pointer.is_constant())
    {
      const constant_exprt &constant = to_constant_expr(pointer);

      if(is_null_pointer(constant))
      {
        address=0;
        return true;
      }
      else if(!to_integer(constant, address))
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
          pointer_type.base_type() = new_index_expr.type();

          typecast_exprt typecast_expr(
            from_integer((*step_size) * (*index) + address, c_index_type()),
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
          pointer_type.base_type() = new_member_expr.type();
          typecast_exprt typecast_expr(
            from_integer(address + *offset, c_index_type()), pointer_type);
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
    auto offset = compute_pointer_offset(to_address_of_expr(ptr).object(), ns);

    if(offset.has_value())
      return from_integer(*offset, expr.type());
  }
  else if(ptr.id()==ID_typecast) // pointer typecast
  {
    const auto &op = to_typecast_expr(ptr).op();
    const typet &op_type = op.type();

    if(op_type.id()==ID_pointer)
    {
      // Cast from pointer to pointer.
      // This just passes through, remove typecast.
      auto new_expr = expr;
      new_expr.op() = op;

      return changed(simplify_pointer_offset(new_expr)); // recursive call
    }
    else if(op_type.id()==ID_signedbv ||
            op_type.id()==ID_unsignedbv)
    {
      // Cast from integer to pointer, say (int *)x.

      if(op.is_constant())
      {
        // (T *)0x1234 -> 0x1234
        return changed(simplify_typecast(typecast_exprt{op, expr.type()}));
      }
      else
      {
        // We do a bit of special treatment for (TYPE *)(a+(int)&o),
        // which is re-written to 'a'.

        typet type = expr.type();
        exprt tmp = op;
        if(tmp.id()==ID_plus && tmp.operands().size()==2)
        {
          const auto &plus_expr = to_plus_expr(tmp);

          if(
            plus_expr.op0().id() == ID_typecast &&
            to_typecast_expr(plus_expr.op0()).op().id() == ID_address_of)
          {
            auto new_expr =
              typecast_exprt::conditional_cast(plus_expr.op1(), type);

            return changed(simplify_node(new_expr));
          }
          else if(
            plus_expr.op1().id() == ID_typecast &&
            to_typecast_expr(plus_expr.op1()).op().id() == ID_address_of)
          {
            auto new_expr =
              typecast_exprt::conditional_cast(plus_expr.op0(), type);

            return changed(simplify_node(new_expr));
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
          tmp = simplify_typecast(typecast_exprt(tmp, expr.type()));

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
    exprt pointer_offset_expr =
      simplify_pointer_offset(to_unary_expr(pointer_offset(ptr_expr.front())));

    exprt sum;

    if(int_expr.size()==1)
      sum=int_expr.front();
    else
      sum = simplify_plus(plus_exprt{int_expr, expr.type()});

    exprt size_expr = from_integer(*element_size, expr.type());

    exprt product = simplify_mult(mult_exprt{sum, size_expr});

    auto new_expr = plus_exprt(pointer_offset_expr, product);

    return changed(simplify_plus(new_expr));
  }
  else if(ptr.id()==ID_constant)
  {
    const constant_exprt &c_ptr = to_constant_expr(ptr);

    if(is_null_pointer(c_ptr))
    {
      return from_integer(0, expr.type());
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

      return from_integer(number, expr.type());
    }
  }

  return unchanged(expr);
}

simplify_exprt::resultt<> simplify_exprt::simplify_inequality_address_of(
  const binary_relation_exprt &expr)
{
  // the operands of the relation are both either one of
  // a) an address_of_exprt
  // b) a typecast_exprt with an address_of_exprt operand

  PRECONDITION(expr.id() == ID_equal || expr.id() == ID_notequal);

  // skip over the typecast
  exprt tmp0 = skip_typecast(expr.op0());
  PRECONDITION(tmp0.id() == ID_address_of);

  auto &tmp0_address_of = to_address_of_expr(tmp0);

  if(
    tmp0_address_of.object().id() == ID_index &&
    to_index_expr(tmp0_address_of.object()).index().is_zero())
  {
    tmp0_address_of =
      address_of_exprt(to_index_expr(tmp0_address_of.object()).array());
  }

  // skip over the typecast
  exprt tmp1 = skip_typecast(expr.op1());
  PRECONDITION(tmp1.id() == ID_address_of);

  auto &tmp1_address_of = to_address_of_expr(tmp1);

  if(
    tmp1_address_of.object().id() == ID_index &&
    to_index_expr(tmp1_address_of.object()).index().is_zero())
  {
    tmp1 = address_of_exprt(to_index_expr(tmp1_address_of.object()).array());
  }

  const auto &tmp0_object = tmp0_address_of.object();
  const auto &tmp1_object = tmp1_address_of.object();

  if(tmp0_object.id() == ID_symbol && tmp1_object.id() == ID_symbol)
  {
    bool equal = to_symbol_expr(tmp0_object).get_identifier() ==
                 to_symbol_expr(tmp1_object).get_identifier();

    return make_boolean_expr(expr.id() == ID_equal ? equal : !equal);
  }
  else if(
    tmp0_object.id() == ID_dynamic_object &&
    tmp1_object.id() == ID_dynamic_object)
  {
    bool equal = to_dynamic_object_expr(tmp0_object).get_instance() ==
                 to_dynamic_object_expr(tmp1_object).get_instance();

    return make_boolean_expr(expr.id() == ID_equal ? equal : !equal);
  }
  else if(
    (tmp0_object.id() == ID_symbol && tmp1_object.id() == ID_dynamic_object) ||
    (tmp0_object.id() == ID_dynamic_object && tmp1_object.id() == ID_symbol))
  {
    return make_boolean_expr(expr.id() != ID_equal);
  }

  return unchanged(expr);
}

simplify_exprt::resultt<> simplify_exprt::simplify_inequality_pointer_object(
  const binary_relation_exprt &expr)
{
  PRECONDITION(expr.id() == ID_equal || expr.id() == ID_notequal);
  PRECONDITION(expr.type().id() == ID_bool);

  exprt::operandst new_inequality_ops;
  forall_operands(it, expr)
  {
    PRECONDITION(it->id() == ID_pointer_object);
    const exprt &op = to_unary_expr(*it).op();

    if(op.id()==ID_address_of)
    {
      const auto &op_object = to_address_of_expr(op).object();

      if((op_object.id() != ID_symbol && op_object.id() != ID_dynamic_object &&
          op_object.id() != ID_string_constant))
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
      new_inequality_ops.push_back(
        simplify_node(typecast_exprt::conditional_cast(
          op, new_inequality_ops.front().type())));
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

    auto p_o_false = expr;
    p_o_false.op() = if_expr.false_case();

    auto p_o_true = expr;
    p_o_true.op() = if_expr.true_case();

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
simplify_exprt::simplify_is_dynamic_object(const unary_exprt &expr)
{
  auto new_expr = expr;
  exprt &op = new_expr.op();

  if(op.id()==ID_if && op.operands().size()==3)
  {
    if_exprt if_expr=lift_if(expr, 0);
    if_expr.true_case() =
      simplify_is_dynamic_object(to_unary_expr(if_expr.true_case()));
    if_expr.false_case() =
      simplify_is_dynamic_object(to_unary_expr(if_expr.false_case()));
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
  if(op.id() == ID_constant && is_null_pointer(to_constant_expr(op)))
    return false_exprt();

  // &something depends on the something
  if(op.id() == ID_address_of)
  {
    const auto &op_object = to_address_of_expr(op).object();

    if(op_object.id() == ID_symbol)
    {
      const irep_idt identifier = to_symbol_expr(op_object).get_identifier();

      // this is for the benefit of symex
      return make_boolean_expr(
        has_prefix(id2string(identifier), SYMEX_DYNAMIC_PREFIX));
    }
    else if(op_object.id() == ID_string_constant)
    {
      return false_exprt();
    }
    else if(op_object.id() == ID_array)
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
simplify_exprt::simplify_is_invalid_pointer(const unary_exprt &expr)
{
  auto new_expr = expr;
  exprt &op = new_expr.op();
  bool no_change = true;

  auto op_result = simplify_object(op);

  if(op_result.has_changed())
  {
    op = op_result.expr;
    no_change = false;
  }

  // NULL is not invalid
  if(op.id() == ID_constant && is_null_pointer(to_constant_expr(op)))
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

  if(op.id() == ID_address_of)
  {
    const auto &op_object = to_address_of_expr(op).object();

    if(op_object.id() == ID_symbol)
    {
      // just get the type
      auto size_opt = size_of_expr(op_object.type(), ns);

      if(size_opt.has_value())
      {
        const typet &expr_type = expr.type();
        exprt size = size_opt.value();

        if(size.type() != expr_type)
          size = simplify_typecast(typecast_exprt(size, expr_type));

        return size;
      }
    }
    else if(op_object.id() == ID_string_constant)
    {
      typet type=expr.type();
      return from_integer(
        to_string_constant(op_object).get_value().size() + 1, type);
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
  return changed(simplify_rec(def));
}
