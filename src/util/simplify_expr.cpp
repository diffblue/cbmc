/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr.h"

#include <algorithm>

#include "arith_tools.h"
#include "base_type.h"
#include "byte_operators.h"
#include "c_types.h"
#include "config.h"
#include "endianness_map.h"
#include "expr_util.h"
#include "fixedbv.h"
#include "invariant.h"
#include "namespace.h"
#include "pointer_offset_size.h"
#include "rational.h"
#include "rational_tools.h"
#include "simplify_utils.h"
#include "std_expr.h"
#include "type_eq.h"

// #define DEBUGX

#ifdef DEBUGX
#include <iostream>
#endif

#include "simplify_expr_class.h"

// #define USE_CACHE

#ifdef USE_CACHE
struct simplify_expr_cachet
{
public:
  #if 1
  typedef std::unordered_map<
    exprt, exprt, irep_full_hash, irep_full_eq> containert;
  #else
  typedef std::unordered_map<exprt, exprt, irep_hash> containert;
  #endif

  containert container_normal;

  containert &container()
  {
    return container_normal;
  }
};

simplify_expr_cachet simplify_expr_cache;
#endif

bool simplify_exprt::simplify_abs(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  if(expr.op0().is_constant())
  {
    const typet &type=ns.follow(expr.op0().type());

    if(type.id()==ID_floatbv)
    {
      ieee_floatt value(to_constant_expr(expr.op0()));
      value.set_sign(false);
      expr=value.to_expr();
      return false;
    }
    else if(type.id()==ID_signedbv ||
            type.id()==ID_unsignedbv)
    {
      auto value = numeric_cast<mp_integer>(expr.op0());
      if(value.has_value())
      {
        if(*value >= 0)
        {
          expr=expr.op0();
          return false;
        }
        else
        {
          value->negate();
          expr = from_integer(*value, type);
          return false;
        }
      }
    }
  }

  return true;
}

bool simplify_exprt::simplify_sign(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  if(expr.op0().is_constant())
  {
    const typet &type=ns.follow(expr.op0().type());

    if(type.id()==ID_floatbv)
    {
      ieee_floatt value(to_constant_expr(expr.op0()));
      expr.make_bool(value.get_sign());
      return false;
    }
    else if(type.id()==ID_signedbv ||
            type.id()==ID_unsignedbv)
    {
      const auto value = numeric_cast<mp_integer>(expr.op0());
      if(value.has_value())
      {
        expr.make_bool(*value >= 0);
        return false;
      }
    }
  }

  return true;
}

bool simplify_exprt::simplify_popcount(popcount_exprt &expr)
{
  const exprt &op = expr.op();

  if(op.is_constant())
  {
    const typet &op_type = op.type();

    if(op_type.id() == ID_signedbv || op_type.id() == ID_unsignedbv)
    {
      const auto width = to_bitvector_type(op_type).get_width();
      const auto &value = to_constant_expr(op).get_value();
      std::size_t result = 0;

      for(std::size_t i = 0; i < width; i++)
        if(get_bvrep_bit(value, width, i))
          result++;

      auto result_expr = from_integer(result, expr.type());
      expr.swap(result_expr);

      return false;
    }
  }

  return true;
}

bool simplify_exprt::simplify_typecast(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  const typet &expr_type=ns.follow(expr.type());
  const typet &op_type=ns.follow(expr.op0().type());

  // eliminate casts of infinity
  if(expr.op0().id()==ID_infinity)
  {
    typet new_type=expr.type();
    exprt tmp;
    tmp.swap(expr.op0());
    tmp.type()=new_type;
    expr.swap(tmp);
    return false;
  }

  // casts from NULL to any integer
  if(op_type.id()==ID_pointer &&
     expr.op0().is_constant() &&
     to_constant_expr(expr.op0()).get_value()==ID_NULL &&
     (expr_type.id()==ID_unsignedbv || expr_type.id()==ID_signedbv) &&
     config.ansi_c.NULL_is_zero)
  {
    exprt tmp=from_integer(0, expr_type);
    expr.swap(tmp);
    return false;
  }

  // casts from pointer to integer
  // where width of integer >= width of pointer
  // (void*)(intX)expr -> (void*)expr
  if(expr_type.id()==ID_pointer &&
     expr.op0().id()==ID_typecast &&
     expr.op0().operands().size()==1 &&
     (op_type.id()==ID_signedbv || op_type.id()==ID_unsignedbv) &&
     to_bitvector_type(op_type).get_width()>=
     to_bitvector_type(expr_type).get_width())
  {
    exprt tmp=expr.op0().op0();
    expr.op0().swap(tmp);
    simplify_typecast(expr); // rec. call
    return false;
  }

  // eliminate redundant typecasts
  if(type_eq(expr.type(), expr.op0().type(), ns))
  {
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
    return false;
  }

  // eliminate casts to proper bool
  if(expr_type.id()==ID_bool)
  {
    // rewrite (bool)x to x!=0
    binary_relation_exprt inequality;
    inequality.id(op_type.id()==ID_floatbv?ID_ieee_float_notequal:ID_notequal);
    inequality.add_source_location()=expr.source_location();
    inequality.lhs()=expr.op0();
    inequality.rhs()=from_integer(0, op_type);
    CHECK_RETURN(inequality.rhs().is_not_nil());
    simplify_node(inequality);
    expr.swap(inequality);
    return false;
  }

  // circular casts through types shorter than `int`
  if(op_type==signedbv_typet(32) &&
     expr.op0().id()==ID_typecast)
  {
    if(expr_type==c_bool_typet(8) ||
       expr_type==signedbv_typet(8) ||
       expr_type==signedbv_typet(16) ||
       expr_type==unsignedbv_typet(16))
    {
      // We checked that the id was ID_typecast in the enclosing `if`
      const auto &typecast=expr_checked_cast<typecast_exprt>(expr.op0());
      if(typecast.op().type()==expr_type)
      {
        expr=typecast.op0();
        return false;
      }
    }
  }

  // eliminate casts to _Bool
  if(expr_type.id()==ID_c_bool &&
     op_type.id()!=ID_bool)
  {
    // rewrite (_Bool)x to (_Bool)(x!=0)
    exprt inequality = is_not_zero(expr.op0(), ns);
    simplify_node(inequality);
    expr.op0()=inequality;
    simplify_typecast(expr); // recursive call
    return false;
  }

  // eliminate typecasts from NULL
  if(expr_type.id()==ID_pointer &&
     expr.op0().is_constant() &&
     (to_constant_expr(expr.op0()).get_value()==ID_NULL ||
      (expr.op0().is_zero() && config.ansi_c.NULL_is_zero)))
  {
    exprt tmp=expr.op0();
    tmp.type()=expr.type();
    to_constant_expr(tmp).set_value(ID_NULL);
    expr.swap(tmp);
    return false;
  }

  // eliminate duplicate pointer typecasts
  // (T1 *)(T2 *)x -> (T1 *)x
  if(expr_type.id()==ID_pointer &&
     expr.op0().id()==ID_typecast &&
     op_type.id()==ID_pointer &&
     expr.op0().operands().size()==1)
  {
    exprt tmp;
    tmp.swap(expr.op0().op0());
    expr.op0().swap(tmp);
    // recursive call
    simplify_node(expr);
    return false;
  }

  // casts from integer to pointer and back:
  // (int)(void *)int -> (int)(size_t)int
  if((expr_type.id()==ID_signedbv || expr_type.id()==ID_unsignedbv) &&
     expr.op0().id()==ID_typecast &&
     expr.op0().operands().size()==1 &&
     op_type.id()==ID_pointer)
  {
    expr.op0().type()=size_type();
    simplify_typecast(expr.op0()); // rec. call
    simplify_typecast(expr); // rec. call
    return false;
  }

  // mildly more elaborate version of the above:
  // (int)((T*)0 + int) -> (int)(sizeof(T)*(size_t)int) if NULL is zero
  if(config.ansi_c.NULL_is_zero &&
     (expr_type.id()==ID_signedbv || expr_type.id()==ID_unsignedbv) &&
     op_type.id()==ID_pointer &&
     expr.op0().id()==ID_plus &&
     expr.op0().operands().size()==2 &&
     ((expr.op0().op0().id()==ID_typecast &&
     expr.op0().op0().operands().size()==1 &&
       expr.op0().op0().op0().is_zero()) ||
      (expr.op0().op0().is_constant() &&
       to_constant_expr(expr.op0().op0()).get_value()==ID_NULL)))
  {
    auto sub_size = pointer_offset_size(to_pointer_type(op_type).subtype(), ns);
    if(sub_size.has_value())
    {
      // void*
      if(*sub_size == 0 || *sub_size == 1)
        expr.op0()=typecast_exprt(expr.op0().op1(), size_type());
      else
        expr.op0() = mult_exprt(
          from_integer(*sub_size, size_type()),
          typecast_exprt(expr.op0().op1(), size_type()));

      simplify_rec(expr.op0());
      simplify_typecast(expr); // rec. call
      return false;
    }
  }

  // Push a numerical typecast into various integer operations, i.e.,
  // (T)(x OP y) ---> (T)x OP (T)y
  //
  // Doesn't work for many, e.g., pointer difference, floating-point,
  // division, modulo.
  // Many operations fail if the width of T
  // is bigger than that of (x OP y). This includes ID_bitnot and
  // anything that might overflow, e.g., ID_plus.
  //
  if((expr_type.id()==ID_signedbv || expr_type.id()==ID_unsignedbv) &&
     (op_type.id()==ID_signedbv || op_type.id()==ID_unsignedbv))
  {
    bool enlarge=
      to_bitvector_type(expr_type).get_width()>
      to_bitvector_type(op_type).get_width();

    if(!enlarge)
    {
      irep_idt op_id=expr.op0().id();

      if(op_id==ID_plus || op_id==ID_minus || op_id==ID_mult ||
         op_id==ID_unary_minus ||
         op_id==ID_bitxor || op_id==ID_bitor || op_id==ID_bitand)
      {
        exprt result=expr.op0();

        if(result.operands().size()>=1 &&
           base_type_eq(result.op0().type(), result.type(), ns))
        {
          result.type()=expr.type();

          Forall_operands(it, result)
          {
            it->make_typecast(expr.type());
            simplify_typecast(*it); // recursive call
          }

          simplify_node(result); // possibly recursive call
          expr.swap(result);
          return false;
        }
      }
      else if(op_id==ID_ashr || op_id==ID_lshr || op_id==ID_shl)
      {
      }
    }
  }

  // Push a numerical typecast into pointer arithmetic
  // (T)(ptr + int) ---> (T)((size_t)ptr + sizeof(subtype)*(size_t)int)
  //
  if((expr_type.id()==ID_signedbv || expr_type.id()==ID_unsignedbv) &&
     op_type.id()==ID_pointer &&
     expr.op0().id()==ID_plus)
  {
    const auto step = pointer_offset_size(to_pointer_type(op_type).subtype(), ns);

    if(step.has_value() && *step != 0)
    {
      const typet size_t_type(size_type());
      expr.op0().type()=size_t_type;

      for(auto &op : expr.op0().operands())
      {
        if(op.type().id()==ID_pointer)
        {
          op.make_typecast(size_t_type);
        }
        else
        {
          op.make_typecast(size_t_type);
          if(*step > 1)
            op = mult_exprt(from_integer(*step, size_t_type), op);
        }
      }

      simplify_rec(expr);
      return false;
    }
  }

  #if 0
  // (T)(a?b:c) --> a?(T)b:(T)c
  if(expr.op0().id()==ID_if &&
     expr.op0().operands().size()==3)
  {
    typecast_exprt tmp_op1(expr.op0().op1(), expr_type);
    typecast_exprt tmp_op2(expr.op0().op2(), expr_type);
    simplify_typecast(tmp_op1);
    simplify_typecast(tmp_op2);
    expr=if_exprt(expr.op0().op0(), tmp_op1, tmp_op2, expr_type);
    simplify_if(to_if_expr(expr));
    return false;
  }
  #endif

  const irep_idt &expr_type_id=expr_type.id();
  const exprt &operand=expr.op0();
  const irep_idt &op_type_id=op_type.id();

  if(operand.is_constant())
  {
    const irep_idt &value=to_constant_expr(operand).get_value();

    // preserve the sizeof type annotation
    typet c_sizeof_type=
      static_cast<const typet &>(operand.find(ID_C_c_sizeof_type));

    if(op_type_id==ID_integer ||
       op_type_id==ID_natural)
    {
      // from integer to ...

      mp_integer int_value=string2integer(id2string(value));

      if(expr_type_id==ID_bool)
      {
        expr.make_bool(int_value!=0);
        return false;
      }

      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv ||
         expr_type_id==ID_c_enum ||
         expr_type_id==ID_c_bit_field ||
         expr_type_id==ID_integer)
      {
        expr=from_integer(int_value, expr_type);
        return false;
      }
    }
    else if(op_type_id==ID_rational)
    {
    }
    else if(op_type_id==ID_real)
    {
    }
    else if(op_type_id==ID_bool)
    {
      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv ||
         expr_type_id==ID_integer ||
         expr_type_id==ID_natural ||
         expr_type_id==ID_rational ||
         expr_type_id==ID_c_bool ||
         expr_type_id==ID_c_enum ||
         expr_type_id==ID_c_bit_field)
      {
        if(operand.is_true())
        {
          expr=from_integer(1, expr_type);
          CHECK_RETURN(expr.is_not_nil());
          return false;
        }
        else if(operand.is_false())
        {
          expr=from_integer(0, expr_type);
          CHECK_RETURN(expr.is_not_nil());
          return false;
        }
      }
      else if(expr_type_id==ID_c_enum_tag)
      {
        const typet &c_enum_type=ns.follow_tag(to_c_enum_tag_type(expr_type));
        if(c_enum_type.id()==ID_c_enum) // possibly incomplete
        {
          unsigned int_value = operand.is_true() ? 1u : 0u;
          exprt tmp=from_integer(int_value, c_enum_type);
          tmp.type()=expr_type; // we maintain the tag type
          expr=tmp;
          return false;
        }
      }
      else if(expr_type_id==ID_pointer &&
              operand.is_false() &&
              config.ansi_c.NULL_is_zero)
      {
        expr=null_pointer_exprt(to_pointer_type(expr_type));
        return false;
      }
    }
    else if(op_type_id==ID_unsignedbv ||
            op_type_id==ID_signedbv ||
            op_type_id==ID_c_bit_field ||
            op_type_id==ID_c_bool)
    {
      mp_integer int_value;

      if(to_integer(to_constant_expr(operand), int_value))
        return true;

      if(expr_type_id==ID_bool)
      {
        expr.make_bool(int_value!=0);
        return false;
      }

      if(expr_type_id==ID_c_bool)
      {
        expr=from_integer(int_value!=0, expr_type);
        return false;
      }

      if(expr_type_id==ID_integer)
      {
        expr=from_integer(int_value, expr_type);
        return false;
      }

      if(expr_type_id==ID_natural)
      {
        if(int_value>=0)
        {
          expr=from_integer(int_value, expr_type);
          return false;
        }
      }

      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv ||
         expr_type_id==ID_bv ||
         expr_type_id==ID_c_bit_field)
      {
        expr=from_integer(int_value, expr_type);

        if(c_sizeof_type.is_not_nil())
          expr.set(ID_C_c_sizeof_type, c_sizeof_type);

        return false;
      }

      if(expr_type_id==ID_c_enum_tag)
      {
        const typet &c_enum_type=ns.follow_tag(to_c_enum_tag_type(expr_type));
        if(c_enum_type.id()==ID_c_enum) // possibly incomplete
        {
          exprt tmp=from_integer(int_value, c_enum_type);
          tmp.type()=expr_type; // we maintain the tag type
          expr=tmp;
          return false;
        }
      }

      if(expr_type_id==ID_c_enum)
      {
        expr=from_integer(int_value, expr_type);
        return false;
      }

      if(expr_type_id==ID_fixedbv)
      {
        // int to float
        const fixedbv_typet &f_expr_type=
          to_fixedbv_type(expr_type);

        fixedbvt f;
        f.spec=fixedbv_spect(f_expr_type);
        f.from_integer(int_value);
        expr=f.to_expr();

        return false;
      }

      if(expr_type_id==ID_floatbv)
      {
        // int to float
        const floatbv_typet &f_expr_type=
          to_floatbv_type(expr_type);

        ieee_floatt f(f_expr_type);
        f.from_integer(int_value);
        expr=f.to_expr();

        return false;
      }

      if(expr_type_id==ID_rational)
      {
        rationalt r(int_value);
        expr=from_rational(r);
        return false;
      }
    }
    else if(op_type_id==ID_fixedbv)
    {
      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv)
      {
        // cast from fixedbv to int
        fixedbvt f(to_constant_expr(expr.op0()));
        expr=from_integer(f.to_integer(), expr_type);
        return false;
      }
      else if(expr_type_id==ID_fixedbv)
      {
        // fixedbv to fixedbv
        fixedbvt f(to_constant_expr(expr.op0()));
        f.round(fixedbv_spect(to_fixedbv_type(expr_type)));
        expr=f.to_expr();
        return false;
      }
    }
    else if(op_type_id==ID_floatbv)
    {
      ieee_floatt f(to_constant_expr(expr.op0()));

      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv)
      {
        // cast from float to int
        expr=from_integer(f.to_integer(), expr_type);
        return false;
      }
      else if(expr_type_id==ID_floatbv)
      {
        // float to double or double to float
        ieee_floatt f(to_constant_expr(expr.op0()));
        f.change_spec(ieee_float_spect(to_floatbv_type(expr_type)));
        expr=f.to_expr();
        return false;
      }
      else if(expr_type_id==ID_fixedbv)
      {
        fixedbvt fixedbv;
        fixedbv.spec=fixedbv_spect(to_fixedbv_type(expr_type));
        ieee_floatt factor(f.spec);
        factor.from_integer(power(2, fixedbv.spec.get_fraction_bits()));
        f*=factor;
        fixedbv.set_value(f.to_integer());
        expr=fixedbv.to_expr();
        return false;
      }
    }
    else if(op_type_id==ID_bv)
    {
      if(expr_type_id==ID_unsignedbv ||
         expr_type_id==ID_signedbv ||
         expr_type_id==ID_floatbv)
      {
        const auto width = to_bv_type(op_type).get_width();
        const auto int_value = bvrep2integer(value, width, false);
        expr=from_integer(int_value, expr_type);
        return false;
      }
    }
    else if(op_type_id==ID_c_enum_tag) // enum to int
    {
      const typet &base_type =
        to_c_enum_type(ns.follow_tag(to_c_enum_tag_type(op_type))).subtype();
      if(base_type.id()==ID_signedbv || base_type.id()==ID_unsignedbv)
      {
        // enum constants use the representation of their base type
        expr.op0().type()=base_type;
        simplify_typecast(expr);
        return false;
      }
    }
    else if(op_type_id==ID_c_enum) // enum to int
    {
      const typet &base_type=to_c_enum_type(op_type).subtype();
      if(base_type.id()==ID_signedbv || base_type.id()==ID_unsignedbv)
      {
        // enum constants use the representation of their base type
        expr.op0().type()=base_type;
        simplify_typecast(expr);
        return false;
      }
    }
  }
  else if(operand.id()==ID_typecast) // typecast of typecast
  {
    // (T1)(T2)x ---> (T1)
    // where T1 has fewer bits than T2
    if(operand.operands().size()==1 &&
       op_type_id==expr_type_id &&
       (expr_type_id==ID_unsignedbv || expr_type_id==ID_signedbv) &&
       to_bitvector_type(expr_type).get_width()<=
         to_bitvector_type(operand.type()).get_width())
    {
      exprt tmp;
      tmp.swap(expr.op0().op0());
      expr.op0().swap(tmp);
      // might enable further simplification
      simplify_typecast(expr); // recursive call
      return false;
    }
  }
  else if(operand.id()==ID_address_of)
  {
    const exprt &o=to_address_of_expr(operand).object();

    // turn &array into &array[0] when casting to pointer-to-element-type
    if(o.type().id()==ID_array &&
       base_type_eq(expr_type, pointer_type(o.type().subtype()), ns))
    {
      expr=address_of_exprt(index_exprt(o, from_integer(0, size_type())));

      simplify_rec(expr);
      return false;
    }
  }

  return true;
}

bool simplify_exprt::simplify_dereference(exprt &expr)
{
  const exprt &pointer=to_dereference_expr(expr).pointer();

  if(pointer.type().id()!=ID_pointer)
    return true;

  if(pointer.id()==ID_if && pointer.operands().size()==3)
  {
    const if_exprt &if_expr=to_if_expr(pointer);

    exprt tmp_op1=expr;
    tmp_op1.op0()=if_expr.true_case();
    simplify_dereference(tmp_op1);
    exprt tmp_op2=expr;
    tmp_op2.op0()=if_expr.false_case();
    simplify_dereference(tmp_op2);

    expr=if_exprt(if_expr.cond(), tmp_op1, tmp_op2);

    simplify_if(to_if_expr(expr));

    return false;
  }

  if(pointer.id()==ID_address_of)
  {
    exprt tmp=to_address_of_expr(pointer).object();
    // one address_of is gone, try again
    simplify_rec(tmp);
    expr.swap(tmp);
    return false;
  }
  // rewrite *(&a[0] + x) to a[x]
  else if(pointer.id()==ID_plus &&
          pointer.operands().size()==2 &&
          pointer.op0().id()==ID_address_of)
  {
    const address_of_exprt &address_of=
      to_address_of_expr(pointer.op0());
    if(address_of.object().id()==ID_index)
    {
      const index_exprt &old=to_index_expr(address_of.object());
      if(ns.follow(old.array().type()).id()==ID_array)
      {
        index_exprt idx(old.array(),
                        plus_exprt(old.index(), pointer.op1()),
                        ns.follow(old.array().type()).subtype());
        simplify_rec(idx);
        expr.swap(idx);
        return false;
      }
    }
  }

  return true;
}

bool simplify_exprt::simplify_if_implies(
  exprt &expr,
  const exprt &cond,
  bool truth,
  bool &new_truth)
{
  if(expr==cond)
  {
    new_truth = truth;
    return false;
  }

  if(truth && cond.id()==ID_lt && expr.id()==ID_lt)
  {
    if(cond.op0()==expr.op0() &&
       cond.op1().is_constant() &&
       expr.op1().is_constant() &&
       cond.op1().type()==expr.op1().type())
    {
      mp_integer i1, i2;

      if(
        !to_integer(to_constant_expr(cond.op1()), i1) &&
        !to_integer(to_constant_expr(expr.op1()), i2))
      {
        if(i1 >= i2)
        {
          new_truth = true;
          return false;
        }
      }
    }

    if(cond.op1()==expr.op1() &&
       cond.op0().is_constant() &&
       expr.op0().is_constant() &&
       cond.op0().type()==expr.op0().type())
    {
      mp_integer i1, i2;

      if(
        !to_integer(to_constant_expr(cond.op0()), i1) &&
        !to_integer(to_constant_expr(expr.op0()), i2))
      {
        if(i1 <= i2)
        {
          new_truth = true;
          return false;
        }
      }
    }
  }

  return true;
}

bool simplify_exprt::simplify_if_recursive(
  exprt &expr,
  const exprt &cond,
  bool truth)
{
  if(expr.type().id()==ID_bool)
  {
    bool new_truth;

    if(!simplify_if_implies(expr, cond, truth, new_truth))
    {
      if(new_truth)
      {
        expr=true_exprt();
        return false;
      }
      else
      {
        expr=false_exprt();
        return false;
      }
    }
  }

  bool result = true;

  Forall_operands(it, expr)
    result = simplify_if_recursive(*it, cond, truth) && result;

  return result;
}

bool simplify_exprt::simplify_if_conj(
  exprt &expr,
  const exprt &cond)
{
  forall_operands(it, cond)
  {
    if(expr==*it)
    {
      expr=true_exprt();
      return false;
    }
  }

  bool result=true;

  Forall_operands(it, expr)
    result=simplify_if_conj(*it, cond) && result;

  return result;
}

bool simplify_exprt::simplify_if_disj(
  exprt &expr,
  const exprt &cond)
{
  forall_operands(it, cond)
  {
    if(expr==*it)
    {
      expr=false_exprt();
      return false;
    }
  }

  bool result=true;

  Forall_operands(it, expr)
    result=simplify_if_disj(*it, cond) && result;

  return result;
}

bool simplify_exprt::simplify_if_branch(
  exprt &trueexpr,
  exprt &falseexpr,
  const exprt &cond)
{
  bool tresult = true;
  bool fresult = true;

  if(cond.id()==ID_and)
  {
    tresult = simplify_if_conj(trueexpr, cond) && tresult;
    fresult = simplify_if_recursive(falseexpr, cond, false) && fresult;
  }
  else if(cond.id()==ID_or)
  {
    tresult = simplify_if_recursive(trueexpr, cond, true) && tresult;
    fresult = simplify_if_disj(falseexpr, cond) && fresult;
  }
  else
  {
    tresult = simplify_if_recursive(trueexpr, cond, true) && tresult;
    fresult = simplify_if_recursive(falseexpr, cond, false) && fresult;
  }

  if(!tresult)
    simplify_rec(trueexpr);
  if(!fresult)
    simplify_rec(falseexpr);

  return tresult && fresult;
}

bool simplify_exprt::simplify_if_cond(exprt &expr)
{
  bool result=true;
  bool tmp=false;

  while(!tmp)
  {
    tmp=true;

    if(expr.id()==ID_and)
    {
      if(expr.has_operands())
      {
        exprt::operandst &operands = expr.operands();
        for(exprt::operandst::iterator it1=operands.begin();
            it1!=operands.end(); it1++)
        {
          for(exprt::operandst::iterator it2=operands.begin();
              it2!=operands.end(); it2++)
          {
            if(it1!=it2)
              tmp=simplify_if_recursive(*it1, *it2, true) && tmp;
          }
        }
      }
    }

    if(!tmp)
      simplify_rec(expr);

    result=tmp && result;
  }

  return result;
}

bool simplify_exprt::simplify_if_preorder(if_exprt &expr)
{
  exprt &cond=expr.cond();
  exprt &truevalue=expr.true_case();
  exprt &falsevalue=expr.false_case();

  // we first want to look at the condition
  bool result=simplify_rec(cond);

  // 1 ? a : b -> a  and  0 ? a : b -> b
  if(cond.is_constant())
  {
    exprt tmp=cond.is_true()?truevalue:falsevalue;
    simplify_rec(tmp);
    expr.swap(tmp);
    return false;
  }

  if(do_simplify_if)
  {
    if(cond.id()==ID_not)
    {
      exprt tmp;
      tmp.swap(cond.op0());
      cond.swap(tmp);
      truevalue.swap(falsevalue);
      result=false;
    }

#ifdef USE_LOCAL_REPLACE_MAP
    replace_mapt map_before(local_replace_map);

    // a ? b : c  --> a ? b[a/true] : c
    if(cond.id()==ID_and)
    {
      forall_operands(it, cond)
      {
        if(it->id()==ID_not)
          local_replace_map.insert(
            std::make_pair(it->op0(), false_exprt()));
        else
          local_replace_map.insert(
            std::make_pair(*it, true_exprt()));
      }
    }
    else
      local_replace_map.insert(std::make_pair(cond, true_exprt()));

    result=simplify_rec(truevalue) && result;

    local_replace_map=map_before;

    // a ? b : c  --> a ? b : c[a/false]
    if(cond.id()==ID_or)
    {
      forall_operands(it, cond)
      {
        if(it->id()==ID_not)
          local_replace_map.insert(
            std::make_pair(it->op0(), true_exprt()));
        else
          local_replace_map.insert(
            std::make_pair(*it, false_exprt()));
      }
    }
    else
      local_replace_map.insert(std::make_pair(cond, false_exprt()));

    result=simplify_rec(falsevalue) && result;

    local_replace_map.swap(map_before);
#else
    result=simplify_rec(truevalue) && result;
    result=simplify_rec(falsevalue) && result;
#endif
  }
  else
  {
    result=simplify_rec(truevalue) && result;
    result=simplify_rec(falsevalue) && result;
  }

  return result;
}

bool simplify_exprt::simplify_if(if_exprt &expr)
{
  exprt &cond=expr.cond();
  exprt &truevalue=expr.true_case();
  exprt &falsevalue=expr.false_case();

  bool result=true;

  if(do_simplify_if)
  {
    #if 0
    result = simplify_if_cond(cond) && result;
    result = simplify_if_branch(truevalue, falsevalue, cond) && result;
    #endif

    if(expr.type()==bool_typet())
    {
      // a?b:c <-> (a && b) || (!a && c)

      if(truevalue.is_true() && falsevalue.is_false())
      {
        // a?1:0 <-> a
        exprt tmp;
        tmp.swap(cond);
        expr.swap(tmp);
        return false;
      }
      else if(truevalue.is_false() && falsevalue.is_true())
      {
        // a?0:1 <-> !a
        exprt tmp;
        tmp.swap(cond);
        tmp.make_not();
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
      else if(falsevalue.is_false())
      {
        // a?b:0 <-> a AND b
        and_exprt tmp(cond, truevalue);
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
      else if(falsevalue.is_true())
      {
        // a?b:1 <-> !a OR b
        or_exprt tmp(cond, truevalue);
        tmp.op0().make_not();
        simplify_node(tmp.op0());
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
      else if(truevalue.is_true())
      {
        // a?1:b <-> a||(!a && b) <-> a OR b
        or_exprt tmp(cond, falsevalue);
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
      else if(truevalue.is_false())
      {
        // a?0:b <-> !a && b
        and_exprt tmp(cond, falsevalue);
        tmp.op0().make_not();
        simplify_node(tmp.op0());
        simplify_node(tmp);
        expr.swap(tmp);
        return false;
      }
    }
  }

  if(truevalue==falsevalue)
  {
    exprt tmp;
    tmp.swap(truevalue);
    expr.swap(tmp);
    return false;
  }

  if(((truevalue.id()==ID_struct && falsevalue.id()==ID_struct) ||
      (truevalue.id()==ID_array && falsevalue.id()==ID_array)) &&
     truevalue.operands().size()==falsevalue.operands().size())
  {
    exprt cond_copy=cond;
    exprt falsevalue_copy=falsevalue;
    expr.swap(truevalue);

    exprt::operandst::const_iterator f_it=
      falsevalue_copy.operands().begin();
    Forall_operands(it, expr)
    {
      if_exprt if_expr(cond_copy, *it, *f_it);
      it->swap(if_expr);
      simplify_if(to_if_expr(*it));
      ++f_it;
    }

    return false;
  }

  return result;
}

bool simplify_exprt::get_values(
  const exprt &expr,
  value_listt &value_list)
{
  if(expr.is_constant())
  {
    mp_integer int_value;
    if(to_integer(to_constant_expr(expr), int_value))
      return true;

    value_list.insert(int_value);

    return false;
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()!=3)
      return true;

    return get_values(expr.op1(), value_list) ||
           get_values(expr.operands().back(), value_list);
  }

  return true;
}

bool simplify_exprt::simplify_lambda(exprt &)
{
  bool result=true;

  return result;
}

bool simplify_exprt::simplify_with(exprt &expr)
{
  bool result=true;

  if((expr.operands().size()%2)!=1)
    return true;

  const typet op0_type=ns.follow(expr.op0().type());

  // now look at first operand

  if(op0_type.id()==ID_struct)
  {
    if(expr.op0().id()==ID_struct ||
       expr.op0().id()==ID_constant)
    {
      while(expr.operands().size()>1)
      {
        const irep_idt &component_name=
          expr.op1().get(ID_component_name);

        if(!to_struct_type(op0_type).
           has_component(component_name))
          return result;

        std::size_t number=to_struct_type(op0_type).
           component_number(component_name);

        expr.op0().operands()[number].swap(expr.op2());

        expr.operands().erase(++expr.operands().begin());
        expr.operands().erase(++expr.operands().begin());

        result=false;
      }
    }
  }
  else if(expr.op0().type().id()==ID_array)
  {
    if(expr.op0().id()==ID_array ||
       expr.op0().id()==ID_constant)
    {
      while(expr.operands().size()>1)
      {
        const auto i = numeric_cast<mp_integer>(expr.op1());

        if(!i.has_value())
          break;

        if(*i < 0 || *i >= expr.op0().operands().size())
          break;

        expr.op0().operands()[numeric_cast_v<std::size_t>(*i)].swap(expr.op2());

        expr.operands().erase(++expr.operands().begin());
        expr.operands().erase(++expr.operands().begin());

        result=false;
      }
    }
  }

  if(expr.operands().size()==1)
  {
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
    result=false;
  }

  return result;
}

bool simplify_exprt::simplify_update(exprt &expr)
{
  if(expr.operands().size()!=3)
    return true;

  // this is to push updates into (possibly nested) constants

  const exprt::operandst &designator=to_update_expr(expr).designator();

  exprt updated_value=to_update_expr(expr).old();
  exprt *value_ptr=&updated_value;

  for(const auto &e : designator)
  {
    const typet &value_ptr_type=ns.follow(value_ptr->type());

    if(e.id()==ID_index_designator &&
       value_ptr->id()==ID_array)
    {
      const auto i = numeric_cast<mp_integer>(e.op0());

      if(!i.has_value())
        return true;

      if(*i < 0 || *i >= value_ptr->operands().size())
        return true;

      value_ptr = &value_ptr->operands()[numeric_cast_v<std::size_t>(*i)];
    }
    else if(e.id()==ID_member_designator &&
            value_ptr->id()==ID_struct)
    {
      const irep_idt &component_name=
        e.get(ID_component_name);
      const struct_typet &value_ptr_struct_type =
        to_struct_type(value_ptr_type);
      if(!value_ptr_struct_type.has_component(component_name))
        return true;
      auto &designator_as_struct_expr = to_struct_expr(*value_ptr);
      value_ptr = &designator_as_struct_expr.component(component_name, ns);
      CHECK_RETURN(value_ptr->is_not_nil());
    }
    else
      return true; // give up, unknown designator
  }

  // found, done
  *value_ptr=to_update_expr(expr).new_value();
  expr.swap(updated_value);

  return false;
}

bool simplify_exprt::simplify_object(exprt &expr)
{
  if(expr.id()==ID_plus)
  {
    if(expr.type().id()==ID_pointer)
    {
      // kill integers from sum
      Forall_operands(it, expr)
        if(ns.follow(it->type()).id()==ID_pointer)
        {
          exprt tmp=*it;
          expr.swap(tmp);
          simplify_object(expr);
          return false;
        }
    }
  }
  else if(expr.id()==ID_typecast)
  {
    auto const &typecast_expr = to_typecast_expr(expr);
    const typet &op_type = ns.follow(typecast_expr.op().type());

    if(op_type.id()==ID_pointer)
    {
      // cast from pointer to pointer
      expr = typecast_expr.op();
      simplify_object(expr);
      return false;
    }
    else if(op_type.id()==ID_signedbv || op_type.id()==ID_unsignedbv)
    {
      // cast from integer to pointer

      // We do a bit of special treatment for (TYPE *)(a+(int)&o) and
      // (TYPE *)(a+(int)((T*)&o+x)), which are re-written to '&o'.

      const exprt &casted_expr = typecast_expr.op();
      if(casted_expr.id() == ID_plus && casted_expr.operands().size() == 2)
      {
        const exprt &cand = casted_expr.op0().id() == ID_typecast
                              ? casted_expr.op0()
                              : casted_expr.op1();

        if(cand.id()==ID_typecast &&
           cand.operands().size()==1 &&
           cand.op0().id()==ID_address_of)
        {
          expr=cand.op0();
          return false;
        }
        else if(cand.id()==ID_typecast &&
                cand.operands().size()==1 &&
                cand.op0().id()==ID_plus &&
                cand.op0().operands().size()==2 &&
                cand.op0().op0().id()==ID_typecast &&
                cand.op0().op0().operands().size()==1 &&
                cand.op0().op0().op0().id()==ID_address_of)
        {
          expr=cand.op0().op0().op0();
          return false;
        }
      }
    }
  }
  else if(expr.id()==ID_address_of)
  {
    if(expr.operands().size()==1)
    {
      if(expr.op0().id()==ID_index && expr.op0().operands().size()==2)
      {
        // &some[i] -> &some
        address_of_exprt new_expr(expr.op0().op0());
        expr.swap(new_expr);
        simplify_object(expr); // recursion
        return false;
      }
      else if(expr.op0().id()==ID_member && expr.op0().operands().size()==1)
      {
        // &some.f -> &some
        address_of_exprt new_expr(expr.op0().op0());
        expr.swap(new_expr);
        simplify_object(expr); // recursion
        return false;
      }
    }
  }

  return true;
}

exprt simplify_exprt::bits2expr(
  const std::string &bits,
  const typet &_type,
  bool little_endian)
{
  // bits start at lowest memory address
  const typet &type=ns.follow(_type);

  auto type_bits = pointer_offset_bits(type, ns);

  if(!type_bits.has_value() || *type_bits != bits.size())
    return nil_exprt();

  if(type.id()==ID_unsignedbv ||
     type.id()==ID_signedbv ||
     type.id()==ID_floatbv ||
     type.id()==ID_fixedbv)
  {
    endianness_mapt map(type, little_endian, ns);

    std::string tmp=bits;
    for(std::string::size_type i=0; i<bits.size(); ++i)
      tmp[i]=bits[map.map_bit(i)];

    std::reverse(tmp.begin(), tmp.end());

    mp_integer i = binary2integer(tmp, false);
    return constant_exprt(integer2bvrep(i, bits.size()), type);
  }
  else if(type.id()==ID_c_enum)
  {
    exprt val = bits2expr(bits, to_c_enum_type(type).subtype(), little_endian);
    val.type()=type;
    return val;
  }
  else if(type.id()==ID_c_enum_tag)
    return
      bits2expr(
        bits,
        ns.follow_tag(to_c_enum_tag_type(type)),
        little_endian);
  else if(type.id()==ID_union)
  {
    // find a suitable member
    const union_typet &union_type=to_union_type(type);
    const union_typet::componentst &components=
      union_type.components();

    for(const auto &component : components)
    {
      exprt val=bits2expr(bits, component.type(), little_endian);
      if(val.is_nil())
        continue;

      return union_exprt(component.get_name(), val, type);
    }
  }
  else if(type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(type);
    const struct_typet::componentst &components=
      struct_type.components();

    struct_exprt result(type);
    result.reserve_operands(components.size());

    mp_integer m_offset_bits=0;
    for(const auto &component : components)
    {
      const auto m_size = pointer_offset_bits(component.type(), ns);
      CHECK_RETURN(m_size.has_value() && *m_size>=0);

      std::string comp_bits = std::string(
        bits,
        numeric_cast_v<std::size_t>(m_offset_bits),
        numeric_cast_v<std::size_t>(*m_size));

      exprt comp=bits2expr(comp_bits, component.type(), little_endian);
      if(comp.is_nil())
        return nil_exprt();
      result.move_to_operands(comp);

      m_offset_bits += *m_size;
    }

    return std::move(result);
  }
  else if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);

    const std::size_t n_el = numeric_cast_v<std::size_t>(array_type.size());

    const auto el_size_opt = pointer_offset_bits(array_type.subtype(), ns);
    CHECK_RETURN(el_size_opt.has_value() && *el_size_opt > 0);

    const std::size_t el_size = numeric_cast_v<std::size_t>(*el_size_opt);

    array_exprt result(array_type);
    result.reserve_operands(n_el);

    for(std::size_t i=0; i<n_el; ++i)
    {
      std::string el_bits=std::string(bits, i*el_size, el_size);
      exprt el = bits2expr(el_bits, array_type.subtype(), little_endian);
      if(el.is_nil())
        return nil_exprt();
      result.move_to_operands(el);
    }

    return std::move(result);
  }

  return nil_exprt();
}

optionalt<std::string> simplify_exprt::expr2bits(
  const exprt &expr,
  bool little_endian)
{
  // extract bits from lowest to highest memory address
  const typet &type=ns.follow(expr.type());

  if(expr.id()==ID_constant)
  {
    if(type.id()==ID_unsignedbv ||
       type.id()==ID_signedbv ||
       type.id()==ID_c_enum ||
       type.id()==ID_c_enum_tag ||
       type.id()==ID_floatbv ||
       type.id()==ID_fixedbv)
    {
      const auto width = to_bitvector_type(type).get_width();
      const auto &bvrep = to_constant_expr(expr).get_value();

      endianness_mapt map(type, little_endian, ns);

      std::string result(width, ' ');

      for(std::string::size_type i = 0; i < width; ++i)
        result[map.map_bit(i)] = get_bvrep_bit(bvrep, width, i) ? '1' : '0';

      return result;
    }
  }
  else if(expr.id()==ID_union)
  {
    return expr2bits(to_union_expr(expr).op(), little_endian);
  }
  else if(expr.id()==ID_struct)
  {
    std::string result;
    forall_operands(it, expr)
    {
      auto tmp=expr2bits(*it, little_endian);
      if(!tmp.has_value())
        return {}; // failed
      result+=tmp.value();
    }

    return result;
  }
  else if(expr.id()==ID_array)
  {
    std::string result;
    forall_operands(it, expr)
    {
      auto tmp=expr2bits(*it, little_endian);
      if(!tmp.has_value())
        return {}; // failed
      result+=tmp.value();
    }

    return result;
  }

  return {};
}

bool simplify_exprt::simplify_byte_extract(byte_extract_exprt &expr)
{
  // lift up any ID_if on the object
  if(expr.op().id()==ID_if)
  {
    if_exprt if_expr=lift_if(expr, 0);
    simplify_byte_extract(to_byte_extract_expr(if_expr.true_case()));
    simplify_byte_extract(to_byte_extract_expr(if_expr.false_case()));
    simplify_if(if_expr);
    expr.swap(if_expr);
    return false;
  }

  const auto el_size = pointer_offset_bits(expr.type(), ns);

  // byte_extract(byte_extract(root, offset1), offset2) =>
  // byte_extract(root, offset1+offset2)
  if(expr.op().id()==expr.id())
  {
    expr.offset()=plus_exprt(
      to_byte_extract_expr(expr.op()).offset(),
      expr.offset());
    simplify_plus(expr.offset());

    expr.op()=to_byte_extract_expr(expr.op()).op();
    simplify_byte_extract(expr);

    return false;
  }

  // byte_extract(byte_update(root, offset, value), offset) =>
  // value
  if(((expr.id()==ID_byte_extract_big_endian &&
       expr.op().id()==ID_byte_update_big_endian) ||
      (expr.id()==ID_byte_extract_little_endian &&
       expr.op().id()==ID_byte_update_little_endian)) &&
     expr.offset()==expr.op().op1())
  {
    if(base_type_eq(expr.type(), expr.op().op2().type(), ns))
    {
      exprt tmp=expr.op().op2();
      expr.swap(tmp);

      return false;
    }
    else if(
      el_size.has_value() &&
      *el_size <= pointer_offset_bits(expr.op().op2().type(), ns))
    {
      expr.op()=expr.op().op2();
      expr.offset()=from_integer(0, expr.offset().type());

      simplify_byte_extract(expr);

      return false;
    }
  }

  // the following require a constant offset
  auto offset = numeric_cast<mp_integer>(expr.offset());
  if(!offset.has_value() || *offset < 0)
    return true;

  // don't do any of the following if endianness doesn't match, as
  // bytes need to be swapped
  if(*offset == 0 && byte_extract_id() == expr.id())
  {
    // byte extract of full object is object
    if(base_type_eq(expr.type(), expr.op().type(), ns))
    {
      exprt tmp = expr.op();
      expr.swap(tmp);

      return false;
    }
    else if(
      expr.type().id() == ID_pointer && expr.op().type().id() == ID_pointer)
    {
      typecast_exprt tc(expr.op(), expr.type());
      expr.swap(tc);

      return false;
    }
  }

  // no proper simplification for expr.type()==void
  // or types of unknown size
  if(!el_size.has_value() || *el_size == 0)
    return true;

  if(expr.op().id()==ID_array_of &&
     to_array_of_expr(expr.op()).op().id()==ID_constant)
  {
    const auto const_bits_opt=
      expr2bits(to_array_of_expr(expr.op()).op(),
                byte_extract_id()==ID_byte_extract_little_endian);

    if(!const_bits_opt.has_value())
      return true;

    std::string const_bits=const_bits_opt.value();

    DATA_INVARIANT(!const_bits.empty(), "bit representation must be non-empty");

    // double the string until we have sufficiently many bits
    while(mp_integer(const_bits.size()) < *offset * 8 + *el_size)
      const_bits+=const_bits;

    std::string el_bits = std::string(
      const_bits,
      numeric_cast_v<std::size_t>(*offset * 8),
      numeric_cast_v<std::size_t>(*el_size));

    exprt tmp=
      bits2expr(
        el_bits,
        expr.type(),
        expr.id()==ID_byte_extract_little_endian);

    if(tmp.is_not_nil())
    {
      expr.swap(tmp);
      return false;
    }
  }

  // in some cases we even handle non-const array_of
  if(
    expr.op().id() == ID_array_of && (*offset * 8) % (*el_size) == 0 &&
    *el_size <= pointer_offset_bits(expr.op().op0().type(), ns))
  {
    expr.op()=index_exprt(expr.op(), expr.offset());
    expr.offset()=from_integer(0, expr.offset().type());
    simplify_rec(expr);

    return false;
  }

  // extract bits of a constant
  const auto bits=
    expr2bits(expr.op(), expr.id()==ID_byte_extract_little_endian);

  // exact match of length only - otherwise we might lose bits of
  // flexible array members at the end of a struct
  if(bits.has_value() && mp_integer(bits->size()) == *el_size + *offset * 8)
  {
    std::string bits_cut = std::string(
      bits.value(),
      numeric_cast_v<std::size_t>(*offset * 8),
      numeric_cast_v<std::size_t>(*el_size));

    exprt tmp=
      bits2expr(
        bits_cut,
        expr.type(),
        expr.id()==ID_byte_extract_little_endian);

    if(tmp.is_not_nil())
    {
      expr.swap(tmp);

      return false;
    }
  }

  // try to refine it down to extracting from a member or an index in an array
  exprt subexpr =
    get_subexpression_at_offset(expr.op(), *offset, expr.type(), ns);
  if(subexpr.is_nil() || subexpr == expr)
    return true;

  simplify_rec(subexpr);
  expr.swap(subexpr);
  return false;
}

bool simplify_exprt::simplify_byte_update(byte_update_exprt &expr)
{
  // byte_update(byte_update(root, offset, value), offset, value2) =>
  // byte_update(root, offset, value2)
  if(expr.id()==expr.op().id() &&
     expr.offset()==expr.op().op1() &&
     base_type_eq(expr.value().type(), expr.op().op2().type(), ns))
  {
    expr.op()=expr.op().op0();
    return false;
  }

  const exprt &root=expr.op();
  const exprt &offset=expr.offset();
  const exprt &value=expr.value();
  const auto val_size = pointer_offset_bits(value.type(), ns);
  const auto root_size = pointer_offset_bits(root.type(), ns);

  // byte update of full object is byte_extract(new value)
  if(
    offset.is_zero() && val_size.has_value() && *val_size > 0 &&
    root_size.has_value() && *root_size > 0 && *val_size >= *root_size)
  {
    byte_extract_exprt be(
      expr.id()==ID_byte_update_little_endian ?
        ID_byte_extract_little_endian :
        ID_byte_extract_big_endian,
      value, offset, expr.type());

    simplify_byte_extract(be);
    expr.swap(be);

    return false;
  }

  /*
   * byte_update(root, offset,
   *             extract(root, offset) WITH component:=value)
   * =>
   * byte_update(root, offset + component offset,
   *             value)
   */

  if(expr.id()!=ID_byte_update_little_endian)
    return true;

  if(value.id()==ID_with)
  {
    const with_exprt &with=to_with_expr(value);

    if(with.old().id()==ID_byte_extract_little_endian)
    {
      const byte_extract_exprt &extract=to_byte_extract_expr(with.old());

      /* the simplification can be used only if
         root and offset of update and extract
         are the same */
      if(!(root==extract.op()))
        return true;
      if(!(offset==extract.offset()))
        return true;

      const typet &tp=ns.follow(with.type());
      if(tp.id()==ID_struct)
      {
        const struct_typet &struct_type=to_struct_type(tp);
        const irep_idt &component_name=with.where().get(ID_component_name);
        const typet &c_type = struct_type.get_component(component_name).type();

        // is this a bit field?
        if(c_type.id() == ID_c_bit_field || c_type.id() == ID_bool)
        {
          // don't touch -- might not be byte-aligned
        }
        else
        {
          // new offset = offset + component offset
          auto i = member_offset(struct_type, component_name, ns);
          if(i.has_value())
          {
            exprt compo_offset = from_integer(*i, offset.type());
            plus_exprt new_offset(offset, compo_offset);
            simplify_node(new_offset);
            exprt new_value(with.op2());
            expr.op1().swap(new_offset);
            expr.op2().swap(new_value);
            simplify_byte_update(expr); // do this recursively
            return false;
          }
        }
      }
      else if(tp.id()==ID_array)
      {
        auto i = pointer_offset_size(to_array_type(tp).subtype(), ns);
        if(i.has_value())
        {
          const exprt &index=with.where();
          mult_exprt index_offset(index, from_integer(*i, index.type()));
          simplify_node(index_offset);

          // index_offset may need a typecast
          if(!base_type_eq(offset.type(), index.type(), ns))
          {
            typecast_exprt tmp(index_offset, offset.type());
            simplify_node(tmp);
            index_offset.swap(tmp);
          }

          plus_exprt new_offset(offset, index_offset);
          simplify_node(new_offset);
          exprt new_value(with.op2());
          expr.op1().swap(new_offset);
          expr.op2().swap(new_value);
          simplify_byte_update(expr); // do this recursively
          return false;
        }
      }
    }
  }

  // the following require a constant offset
  const auto offset_int = numeric_cast<mp_integer>(offset);
  if(!offset_int.has_value() || *offset_int < 0)
    return true;

  const typet &op_type=ns.follow(root.type());

  // size must be known
  if(!val_size.has_value() || *val_size == 0)
    return true;

  // Are we updating (parts of) a struct? Do individual member updates
  // instead, unless there are non-byte-sized bit fields
  if(op_type.id()==ID_struct)
  {
    exprt result_expr;
    result_expr.make_nil();

    auto update_size = pointer_offset_size(value.type(), ns);

    const struct_typet &struct_type=
      to_struct_type(op_type);
    const struct_typet::componentst &components=
      struct_type.components();

    for(const auto &component : components)
    {
      auto m_offset = member_offset(struct_type, component.get_name(), ns);

      auto m_size_bits = pointer_offset_bits(component.type(), ns);

      // can we determine the current offset?
      if(!m_offset.has_value())
      {
        result_expr.make_nil();
        break;
      }

      // is it a byte-sized member?
      if(!m_size_bits.has_value() || *m_size_bits == 0 || (*m_size_bits) % 8 != 0)
      {
        result_expr.make_nil();
        break;
      }

      mp_integer m_size_bytes = (*m_size_bits) / 8;

      // is that member part of the update?
      if(*m_offset + m_size_bytes <= *offset_int)
        continue;
      // are we done updating?
      else if(
        update_size.has_value() && *update_size > 0 &&
        *m_offset >= *offset_int + *update_size)
      {
        break;
      }

      if(result_expr.is_nil())
        result_expr=expr.op();

      exprt member_name(ID_member_name);
      member_name.set(ID_component_name, component.get_name());
      result_expr=with_exprt(result_expr, member_name, nil_exprt());

      // are we updating on member boundaries?
      if(
        *m_offset < *offset_int ||
        (*m_offset == *offset_int && update_size.has_value() &&
         *update_size > 0 && m_size_bytes > *update_size))
      {
        byte_update_exprt v(
          ID_byte_update_little_endian,
          member_exprt(root, component.get_name(), component.type()),
          from_integer(*offset_int - *m_offset, offset.type()),
          value);

        to_with_expr(result_expr).new_value().swap(v);
      }
      else if(
        update_size.has_value() && *update_size > 0 &&
        *m_offset + m_size_bytes > *offset_int + *update_size)
      {
        // we don't handle this for the moment
        result_expr.make_nil();
        break;
      }
      else
      {
        byte_extract_exprt v(
          ID_byte_extract_little_endian,
          value,
          from_integer(*m_offset - *offset_int, offset.type()),
          component.type());

        to_with_expr(result_expr).new_value().swap(v);
      }
    }

    if(result_expr.is_not_nil())
    {
      simplify_rec(result_expr);
      expr.swap(result_expr);

      return false;
    }

    if(result_expr.is_not_nil())
    {
      simplify_rec(result_expr);
      expr.swap(result_expr);

      return false;
    }
  }

  // replace elements of array or struct expressions, possibly using
  // byte_extract
  if(root.id()==ID_array)
  {
    auto el_size = pointer_offset_bits(op_type.subtype(), ns);

    if(!el_size.has_value() || *el_size == 0 ||
       (*el_size) % 8 != 0 || (*val_size) % 8 != 0)
    {
      return true;
    }

    exprt result=root;

    mp_integer m_offset_bits=0, val_offset=0;
    Forall_operands(it, result)
    {
      if(*offset_int * 8 + (*val_size) <= m_offset_bits)
        break;

      if(*offset_int * 8 < m_offset_bits + *el_size)
      {
        mp_integer bytes_req = (m_offset_bits + *el_size) / 8 - *offset_int;
        bytes_req-=val_offset;
        if(val_offset + bytes_req > (*val_size) / 8)
          bytes_req = (*val_size) / 8 - val_offset;

        byte_extract_exprt new_val(
          byte_extract_id(),
          value,
          from_integer(val_offset, offset.type()),
          array_typet(unsignedbv_typet(8),
                      from_integer(bytes_req, offset.type())));

        *it = byte_update_exprt(
          expr.id(),
          *it,
          from_integer(
            *offset_int + val_offset - m_offset_bits / 8, offset.type()),
          new_val);

        simplify_rec(*it);

        val_offset+=bytes_req;
      }

      m_offset_bits += *el_size;
    }

    expr.swap(result);

    return false;
  }

  return true;
}

bool simplify_exprt::simplify_node_preorder(exprt &expr)
{
  bool result=true;

  // The ifs below could one day be replaced by a switch()

  if(expr.id()==ID_address_of)
  {
    // the argument of this expression needs special treatment
  }
  else if(expr.id()==ID_if)
    result=simplify_if_preorder(to_if_expr(expr));
  else
  {
    if(expr.has_operands())
    {
      Forall_operands(it, expr)
        if(!simplify_rec(*it)) // recursive call
          result=false;
    }
  }

  return result;
}

bool simplify_exprt::simplify_node(exprt &expr)
{
  if(!expr.has_operands())
    return true;

  // #define DEBUGX

  #ifdef DEBUGX
  exprt old(expr);
  #endif

  bool result=true;

  result=sort_and_join(expr) && result;

  if(expr.id()==ID_typecast)
    result=simplify_typecast(expr) && result;
  else if(expr.id()==ID_equal || expr.id()==ID_notequal ||
          expr.id()==ID_gt    || expr.id()==ID_lt ||
          expr.id()==ID_ge    || expr.id()==ID_le)
    result=simplify_inequality(expr) && result;
  else if(expr.id()==ID_if)
    result=simplify_if(to_if_expr(expr)) && result;
  else if(expr.id()==ID_lambda)
    result=simplify_lambda(expr) && result;
  else if(expr.id()==ID_with)
    result=simplify_with(expr) && result;
  else if(expr.id()==ID_update)
    result=simplify_update(expr) && result;
  else if(expr.id()==ID_index)
    result=simplify_index(expr) && result;
  else if(expr.id()==ID_member)
    result=simplify_member(expr) && result;
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
    result=simplify_byte_update(to_byte_update_expr(expr)) && result;
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
    result=simplify_byte_extract(to_byte_extract_expr(expr)) && result;
  else if(expr.id()==ID_pointer_object)
    result=simplify_pointer_object(expr) && result;
  else if(expr.id()==ID_dynamic_object)
    result=simplify_dynamic_object(expr) && result;
  else if(expr.id()==ID_invalid_pointer)
    result=simplify_invalid_pointer(expr) && result;
  else if(expr.id()==ID_object_size)
    result=simplify_object_size(expr) && result;
  else if(expr.id()==ID_good_pointer)
    result=simplify_good_pointer(expr) && result;
  else if(expr.id()==ID_div)
    result=simplify_div(expr) && result;
  else if(expr.id()==ID_mod)
    result=simplify_mod(expr) && result;
  else if(expr.id()==ID_bitnot)
    result=simplify_bitnot(expr) && result;
  else if(expr.id()==ID_bitand ||
          expr.id()==ID_bitor ||
          expr.id()==ID_bitxor)
    result=simplify_bitwise(expr) && result;
  else if(expr.id()==ID_ashr || expr.id()==ID_lshr || expr.id()==ID_shl)
    result=simplify_shifts(expr) && result;
  else if(expr.id()==ID_power)
    result=simplify_power(expr) && result;
  else if(expr.id()==ID_plus)
    result=simplify_plus(expr) && result;
  else if(expr.id()==ID_minus)
    result=simplify_minus(expr) && result;
  else if(expr.id()==ID_mult)
    result=simplify_mult(expr) && result;
  else if(expr.id()==ID_floatbv_plus ||
          expr.id()==ID_floatbv_minus ||
          expr.id()==ID_floatbv_mult ||
          expr.id()==ID_floatbv_div)
    result=simplify_floatbv_op(expr) && result;
  else if(expr.id()==ID_floatbv_typecast)
    result=simplify_floatbv_typecast(expr) && result;
  else if(expr.id()==ID_unary_minus)
    result=simplify_unary_minus(expr) && result;
  else if(expr.id()==ID_unary_plus)
    result=simplify_unary_plus(expr) && result;
  else if(expr.id()==ID_not)
    result=simplify_not(expr) && result;
  else if(expr.id()==ID_implies ||
          expr.id()==ID_or      || expr.id()==ID_xor ||
          expr.id()==ID_and)
    result=simplify_boolean(expr) && result;
  else if(expr.id()==ID_dereference)
    result=simplify_dereference(expr) && result;
  else if(expr.id()==ID_address_of)
    result=simplify_address_of(expr) && result;
  else if(expr.id()==ID_pointer_offset)
    result=simplify_pointer_offset(expr) && result;
  else if(expr.id()==ID_extractbit)
    result=simplify_extractbit(expr) && result;
  else if(expr.id()==ID_concatenation)
    result=simplify_concatenation(expr) && result;
  else if(expr.id()==ID_extractbits)
    result = simplify_extractbits(to_extractbits_expr(expr)) && result;
  else if(expr.id()==ID_ieee_float_equal ||
          expr.id()==ID_ieee_float_notequal)
    result=simplify_ieee_float_relation(expr) && result;
  else if(expr.id() == ID_bswap)
    result = simplify_bswap(to_bswap_expr(expr)) && result;
  else if(expr.id()==ID_isinf)
    result=simplify_isinf(expr) && result;
  else if(expr.id()==ID_isnan)
    result=simplify_isnan(expr) && result;
  else if(expr.id()==ID_isnormal)
    result=simplify_isnormal(expr) && result;
  else if(expr.id()==ID_abs)
    result=simplify_abs(expr) && result;
  else if(expr.id()==ID_sign)
    result=simplify_sign(expr) && result;
  else if(expr.id() == ID_popcount)
    result = simplify_popcount(to_popcount_expr(expr)) && result;

  #ifdef DEBUGX
  if(!result
     #ifdef DEBUG_ON_DEMAND
     && debug_on
     #endif
     )
  {
    std::cout << "===== " << format(old) << "\n ---> " << format(expr)
              << "\n";
  }
  #endif

  return result;
}

/// \return returns true if expression unchanged; returns false if changed
bool simplify_exprt::simplify_rec(exprt &expr)
{
  // look up in cache

  #ifdef USE_CACHE
  std::pair<simplify_expr_cachet::containert::iterator, bool>
    cache_result=simplify_expr_cache.container().
      insert(std::pair<exprt, exprt>(expr, exprt()));

  if(!cache_result.second) // found!
  {
    const exprt &new_expr=cache_result.first->second;

    if(new_expr.id().empty())
      return true; // no change

    expr=new_expr;
    return false;
  }
  #endif

  // We work on a copy to prevent unnecessary destruction of sharing.
  exprt tmp=expr;
  bool result=true;

  result=simplify_node_preorder(tmp);

  if(!simplify_node(tmp))
    result=false;

#ifdef USE_LOCAL_REPLACE_MAP
  #if 1
  replace_mapt::const_iterator it=local_replace_map.find(tmp);
  if(it!=local_replace_map.end())
  {
    tmp=it->second;
    result=false;
  }
  #else
  if(!local_replace_map.empty() &&
     !replace_expr(local_replace_map, tmp))
  {
    simplify_rec(tmp);
    result=false;
  }
  #endif
#endif

  if(!result)
  {
    expr.swap(tmp);

    #ifdef USE_CACHE
    // save in cache
    cache_result.first->second=expr;
    #endif
  }

  return result;
}

bool simplify_exprt::simplify(exprt &expr)
{
#ifdef DEBUG_ON_DEMAND
  if(debug_on)
    std::cout << "TO-SIMP " << format(expr) << "\n";
#endif
  bool res=simplify_rec(expr);
#ifdef DEBUG_ON_DEMAND
  if(debug_on)
    std::cout << "FULLSIMP " << format(expr) << "\n";
#endif
  return res;
}

bool simplify(exprt &expr, const namespacet &ns)
{
  return simplify_exprt(ns).simplify(expr);
}

exprt simplify_expr(const exprt &src, const namespacet &ns)
{
  exprt tmp=src;
  simplify_exprt(ns).simplify(tmp);
  return tmp;
}
