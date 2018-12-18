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
    if(expr.op0().id()==ID_typecast &&
       expr.op0().operands().size()==1 &&
       expr.op0().op0().is_constant() &&
       !to_integer(expr.op0().op0(), address))
      return true;

    if(expr.op0().is_constant())
    {
      if(to_constant_expr(expr.op0()).get_value()==ID_NULL &&
         config.ansi_c.NULL_is_zero) // NULL
      {
        address=0;
        return true;
      }
      else if(!to_integer(expr.op0(), address))
        return true;
    }
  }

  return false;
}

bool simplify_exprt::simplify_address_of_arg(exprt &expr)
{
  if(expr.id()==ID_index)
  {
    if(expr.operands().size()==2)
    {
      bool result=true;
      if(!simplify_address_of_arg(expr.op0()))
        result=false;
      if(!simplify_rec(expr.op1()))
        result=false;

      // rewrite (*(type *)int) [index] by
      // pushing the index inside

      mp_integer address;
      if(is_dereference_integer_object(expr.op0(), address))
      {
        // push index into address
        auto step_size = pointer_offset_size(expr.type(), ns);

        if(step_size.has_value())
        {
          mp_integer index;

          if(!to_integer(expr.op1(), index))
          {
            pointer_typet pointer_type =
              to_pointer_type(to_dereference_expr(expr.op0()).pointer().type());
            pointer_type.subtype() = expr.type();

            typecast_exprt typecast_expr(
              from_integer((*step_size) * index + address, index_type()),
              pointer_type);

            expr = dereference_exprt(typecast_expr, expr.type());
            result = true;
          }
        }
      }

      return result;
    }
  }
  else if(expr.id()==ID_member)
  {
    if(expr.operands().size()==1)
    {
      bool result=true;
      if(!simplify_address_of_arg(expr.op0()))
        result=false;

      const typet &op_type=ns.follow(expr.op0().type());

      if(op_type.id()==ID_struct)
      {
        // rewrite NULL -> member by
        // pushing the member inside

        mp_integer address;
        if(is_dereference_integer_object(expr.op0(), address))
        {
          const struct_typet &struct_type=to_struct_type(op_type);
          const irep_idt &member=to_member_expr(expr).get_component_name();
          auto offset = member_offset(struct_type, member, ns);
          if(offset.has_value())
          {
            pointer_typet pointer_type=
              to_pointer_type(to_dereference_expr(expr.op0()).pointer().type());
            pointer_type.subtype()=expr.type();
            typecast_exprt typecast_expr(
              from_integer(address + *offset, index_type()), pointer_type);
            expr = dereference_exprt(typecast_expr, expr.type());
            result=true;
          }
        }
      }

      return result;
    }
  }
  else if(expr.id()==ID_dereference)
  {
    if(expr.operands().size()==1)
      return simplify_rec(expr.op0());
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()==3)
    {
      bool result=true;
      if(!simplify_rec(expr.op0()))
        result=false;
      if(!simplify_address_of_arg(expr.op1()))
        result=false;
      if(!simplify_address_of_arg(expr.op2()))
        result=false;

      // op0 is a constant?
      if(expr.op0().is_true())
      {
        result=false;
        exprt tmp;
        tmp.swap(expr.op1());
        expr.swap(tmp);
      }
      else if(expr.op0().is_false())
      {
        result=false;
        exprt tmp;
        tmp.swap(expr.op2());
        expr.swap(tmp);
      }

      return result;
    }
  }

  return true;
}

bool simplify_exprt::simplify_address_of(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  if(ns.follow(expr.type()).id()!=ID_pointer)
    return true;

  exprt &object=expr.op0();

  bool result=simplify_address_of_arg(object);

  if(object.id()==ID_index)
  {
    index_exprt &index_expr=to_index_expr(object);

    if(!index_expr.index().is_zero())
    {
      // we normalize &a[i] to (&a[0])+i
      exprt offset;
      offset.swap(index_expr.op1());
      index_expr.op1()=from_integer(0, offset.type());

      expr = plus_exprt(expr, offset);
      return false;
    }
  }
  else if(object.id()==ID_dereference)
  {
    // simplify &*p to p
    auto const &object_as_dereference_expr = to_dereference_expr(object);
    expr = object_as_dereference_expr.pointer();
    return false;
  }

  return result;
}

bool simplify_exprt::simplify_pointer_offset(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  exprt &ptr=expr.op0();

  if(ptr.id()==ID_if && ptr.operands().size()==3)
  {
    if_exprt if_expr=lift_if(expr, 0);
    simplify_pointer_offset(if_expr.true_case());
    simplify_pointer_offset(if_expr.false_case());
    simplify_if(if_expr);
    expr.swap(if_expr);

    return false;
  }

  if(ptr.type().id()!=ID_pointer)
    return true;

  if(ptr.id()==ID_address_of)
  {
    if(ptr.operands().size()!=1)
      return true;

    auto offset = compute_pointer_offset(ptr.op0(), ns);

    if(offset.has_value())
    {
      expr = from_integer(*offset, expr.type());
      return false;
    }
  }
  else if(ptr.id()==ID_typecast) // pointer typecast
  {
    if(ptr.operands().size()!=1)
      return true;

    const typet &op_type=ns.follow(ptr.op0().type());

    if(op_type.id()==ID_pointer)
    {
      // Cast from pointer to pointer.
      // This just passes through, remove typecast.
      exprt tmp=ptr.op0();
      ptr=tmp;

      // recursive call
      simplify_node(expr);
      return false;
    }
    else if(op_type.id()==ID_signedbv ||
            op_type.id()==ID_unsignedbv)
    {
      // Cast from integer to pointer, say (int *)x.

      if(ptr.op0().is_constant())
      {
        // (T *)0x1234 -> 0x1234
        exprt tmp=ptr.op0();
        tmp.make_typecast(expr.type());
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
      else
      {
        // We do a bit of special treatment for (TYPE *)(a+(int)&o),
        // which is re-written to 'a'.

        typet type=ns.follow(expr.type());
        exprt tmp=ptr.op0();
        if(tmp.id()==ID_plus && tmp.operands().size()==2)
        {
          if(tmp.op0().id()==ID_typecast &&
             tmp.op0().operands().size()==1 &&
             tmp.op0().op0().id()==ID_address_of)
          {
            expr=tmp.op1();
            if(type!=expr.type())
              expr.make_typecast(type);

            simplify_node(expr);
            return false;
          }
          else if(tmp.op1().id()==ID_typecast &&
                  tmp.op1().operands().size()==1 &&
                  tmp.op1().op0().id()==ID_address_of)
          {
            expr=tmp.op0();
            if(type!=expr.type())
              expr.make_typecast(type);

            simplify_node(expr);
            return false;
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
          tmp.make_typecast(expr.type());
          simplify_node(tmp);
        }

        int_expr.push_back(tmp);
      }
    }

    if(ptr_expr.size()!=1 || int_expr.empty())
      return true;

    typet pointer_sub_type=ptr_expr.front().type().subtype();
    if(pointer_sub_type.id()==ID_empty)
      pointer_sub_type=char_type();

    auto element_size = pointer_offset_size(pointer_sub_type, ns);

    if(!element_size.has_value())
      return true;

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

    expr=binary_exprt(pointer_offset_expr, ID_plus, product, expr.type());

    simplify_node(expr);

    return false;
  }
  else if(ptr.id()==ID_constant)
  {
    constant_exprt &c_ptr=to_constant_expr(ptr);

    if(c_ptr.get_value()==ID_NULL ||
       c_ptr.value_is_zero_string())
    {
      expr=from_integer(0, expr.type());

      simplify_node(expr);

      return false;
    }
    else
    {
      // this is a pointer, we can't use to_integer
      const auto width = to_pointer_type(ptr.type()).get_width();
      mp_integer number = bvrep2integer(c_ptr.get_value(), width, false);
      // a null pointer would have been caught above, return value 0
      // will indicate that conversion failed
      if(number==0)
        return true;

      // The constant address consists of OBJECT-ID || OFFSET.
      mp_integer offset_bits =
        *pointer_offset_bits(ptr.type(), ns) - config.bv_encoding.object_bits;
      number%=power(2, offset_bits);

      expr=from_integer(number, expr.type());

      simplify_node(expr);

      return false;
    }
  }

  return true;
}

bool simplify_exprt::simplify_inequality_address_of(exprt &expr)
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
    return true;
  if(tmp1.operands().size()!=1)
    return true;

  if(tmp0.op0().id()==ID_symbol &&
     tmp1.op0().id()==ID_symbol)
  {
    bool equal = to_symbol_expr(tmp0.op0()).get_identifier() ==
                 to_symbol_expr(tmp1.op0()).get_identifier();

    expr.make_bool(expr.id()==ID_equal?equal:!equal);

    return false;
  }

  return true;
}

bool simplify_exprt::simplify_inequality_pointer_object(exprt &expr)
{
  PRECONDITION(expr.id() == ID_equal || expr.id() == ID_notequal);
  PRECONDITION(expr.type().id() == ID_bool);
  DATA_INVARIANT(
    expr.operands().size() == 2, "(in)equalities have two operands");

  forall_operands(it, expr)
  {
    PRECONDITION(it->id() == ID_pointer_object);
    PRECONDITION(it->operands().size() == 1);
    const exprt &op=it->op0();

    if(op.id()==ID_address_of)
    {
      if(op.operands().size()!=1 ||
         (op.op0().id()!=ID_symbol &&
          op.op0().id()!=ID_dynamic_object &&
          op.op0().id()!=ID_string_constant))
        return true;
    }
    else if(op.id()!=ID_constant ||
            op.get(ID_value)!=ID_NULL)
      return true;
  }

  bool equal=expr.op0().op0()==expr.op1().op0();

  expr.make_bool(expr.id()==ID_equal?equal:!equal);

  return false;
}

bool simplify_exprt::simplify_pointer_object(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  exprt &op=expr.op0();

  bool result=simplify_object(op);

  if(op.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(op);
    exprt cond=if_expr.cond();

    exprt p_o_false=expr;
    p_o_false.op0()=if_expr.false_case();

    expr.op0()=if_expr.true_case();

    expr=if_exprt(cond, expr, p_o_false, expr.type());
    simplify_rec(expr);

    return false;
  }

  return result;
}

bool simplify_exprt::simplify_dynamic_object(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  exprt &op=expr.op0();

  if(op.id()==ID_if && op.operands().size()==3)
  {
    if_exprt if_expr=lift_if(expr, 0);
    simplify_dynamic_object(if_expr.true_case());
    simplify_dynamic_object(if_expr.false_case());
    simplify_if(if_expr);
    expr.swap(if_expr);

    return false;
  }

  bool result=true;

  if(!simplify_object(op))
    result=false;

  // NULL is not dynamic
  if(op.id()==ID_constant && op.get(ID_value)==ID_NULL)
  {
    expr=false_exprt();
    return false;
  }

  // &something depends on the something
  if(op.id()==ID_address_of && op.operands().size()==1)
  {
    if(op.op0().id()==ID_symbol)
    {
      const irep_idt identifier=to_symbol_expr(op.op0()).get_identifier();

      // this is for the benefit of symex
      expr.make_bool(has_prefix(id2string(identifier), "symex_dynamic::"));
      return false;
    }
    else if(op.op0().id()==ID_string_constant)
    {
      expr=false_exprt();
      return false;
    }
    else if(op.op0().id()==ID_array)
    {
      expr=false_exprt();
      return false;
    }
  }

  return result;
}

bool simplify_exprt::simplify_invalid_pointer(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  exprt &op=expr.op0();

  bool result=true;

  if(!simplify_object(op))
    result=false;

  // NULL is not invalid
  if(op.id()==ID_constant && op.get(ID_value)==ID_NULL)
  {
    expr=false_exprt();
    return false;
  }

  // &anything is not invalid
  if(op.id()==ID_address_of)
  {
    expr=false_exprt();
    return false;
  }

  return result;
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

bool simplify_exprt::simplify_object_size(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  exprt &op=expr.op0();

  bool result=true;

  if(!simplify_object(op))
    result=false;

  if(op.id()==ID_address_of && op.operands().size()==1)
  {
    if(op.op0().id()==ID_symbol)
    {
      // just get the type
      const typet &type=ns.follow(op.op0().type());

      exprt size=size_of_expr(type, ns);

      if(size.is_not_nil())
      {
        const typet &expr_type = expr.type();

        if(size.type() != expr_type)
        {
          size.make_typecast(expr_type);
          simplify_node(size);
        }

        expr=size;
        return false;
      }
    }
    else if(op.op0().id()==ID_string_constant)
    {
      typet type=expr.type();
      expr =
        from_integer(to_string_constant(op.op0()).get_value().size() + 1, type);
      return false;
    }
  }

  return result;
}

bool simplify_exprt::simplify_good_pointer(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  // we expand the definition
  exprt def=good_pointer_def(expr.op0(), ns);

  // recursive call
  simplify_node(def);

  expr.swap(def);

  return false;
}
