/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr_class.h"

#include "arith_tools.h"
#include "expr.h"
#include "ieee_float.h"
#include "invariant.h"
#include "namespace.h"
#include "simplify_expr.h"
#include "std_expr.h"

bool simplify_exprt::simplify_isinf(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  if(ns.follow(expr.op0().type()).id()!=ID_floatbv)
    return true;

  if(expr.op0().is_constant())
  {
    ieee_floatt value(to_constant_expr(expr.op0()));
    expr.make_bool(value.is_infinity());
    return false;
  }

  return true;
}

bool simplify_exprt::simplify_isnan(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  if(expr.op0().is_constant())
  {
    ieee_floatt value(to_constant_expr(expr.op0()));
    expr.make_bool(value.is_NaN());
    return false;
  }

  return true;
}

bool simplify_exprt::simplify_isnormal(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  if(expr.op0().is_constant())
  {
    ieee_floatt value(to_constant_expr(expr.op0()));
    expr.make_bool(value.is_normal());
    return false;
  }

  return true;
}

#if 0
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
      mp_integer value;
      if(!to_integer(expr.op0(), value))
      {
        if(value>=0)
        {
          expr=expr.op0();
          return false;
        }
        else
        {
          value.negate();
          expr=from_integer(value, type);
          return false;
        }
      }
    }
  }

  return true;
}
#endif

#if 0
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
      mp_integer value;
      if(!to_integer(expr.op0(), value))
      {
        expr.make_bool(value>=0);
        return false;
      }
    }
  }

  return true;
}
#endif

bool simplify_exprt::simplify_floatbv_typecast(exprt &expr)
{
  // These casts usually reduce precision, and thus, usually round.

  auto const &floatbv_typecast_expr = to_floatbv_typecast_expr(expr);

  const typet &dest_type = ns.follow(floatbv_typecast_expr.type());
  const typet &src_type = ns.follow(floatbv_typecast_expr.op().type());

  // eliminate redundant casts
  if(dest_type==src_type)
  {
    expr = floatbv_typecast_expr.op();
    return false;
  }

  const exprt &casted_expr = floatbv_typecast_expr.op();
  const exprt &rounding_mode = floatbv_typecast_expr.rounding_mode();

  // We can soundly re-write (float)((double)x op (double)y)
  // to x op y. True for any rounding mode!

  #if 0
  if(casted_expr.id()==ID_floatbv_div ||
     casted_expr.id()==ID_floatbv_mult ||
     casted_expr.id()==ID_floatbv_plus ||
     casted_expr.id()==ID_floatbv_minus)
  {
    if(casted_expr.operands().size()==3 &&
       casted_expr.op0().id()==ID_typecast &&
       casted_expr.op1().id()==ID_typecast &&
       casted_expr.op0().operands().size()==1 &&
       casted_expr.op1().operands().size()==1 &&
       ns.follow(casted_expr.op0().type())==dest_type &&
       ns.follow(casted_expr.op1().type())==dest_type)
    {
      exprt result(casted_expr.id(), floatbv_typecast_expr.type());
      result.operands().resize(3);
      result.op0()=casted_expr.op0().op0();
      result.op1()=casted_expr.op1().op0();
      result.op2()=rounding_mode;

      simplify_node(result);
      expr.swap(result);
      return false;
    }
  }
  #endif

  // constant folding
  if(casted_expr.is_constant() && rounding_mode.is_constant())
  {
    mp_integer rounding_mode_index;
    if(!to_integer(rounding_mode, rounding_mode_index))
    {
      if(src_type.id()==ID_floatbv)
      {
        if(dest_type.id()==ID_floatbv) // float to float
        {
          ieee_floatt result(to_constant_expr(casted_expr));
          result.rounding_mode =
            (ieee_floatt::rounding_modet)numeric_cast_v<std::size_t>(
              rounding_mode_index);
          result.change_spec(
            ieee_float_spect(to_floatbv_type(dest_type)));
          expr=result.to_expr();
          return false;
        }
        else if(dest_type.id()==ID_signedbv ||
                dest_type.id()==ID_unsignedbv)
        {
          if(rounding_mode_index == ieee_floatt::ROUND_TO_ZERO)
          {
            ieee_floatt result(to_constant_expr(casted_expr));
            result.rounding_mode =
              (ieee_floatt::rounding_modet)numeric_cast_v<std::size_t>(
                rounding_mode_index);
            mp_integer value=result.to_integer();
            expr=from_integer(value, dest_type);
            return false;
          }
        }
      }
      else if(src_type.id()==ID_signedbv ||
              src_type.id()==ID_unsignedbv)
      {
        mp_integer value;
        if(!to_integer(casted_expr, value))
        {
          if(dest_type.id()==ID_floatbv) // int to float
          {
            ieee_floatt result(to_floatbv_type(dest_type));
            result.rounding_mode =
              (ieee_floatt::rounding_modet)numeric_cast_v<std::size_t>(
                rounding_mode_index);
            result.from_integer(value);
            expr=result.to_expr();
            return false;
          }
        }
      }
      else if(src_type.id() == ID_c_enum_tag)
      {
        // go through underlying type
        const auto &enum_type = ns.follow_tag(to_c_enum_tag_type(src_type));
        exprt simplified_typecast = simplify_expr(
          typecast_exprt(casted_expr, to_c_enum_type(enum_type).subtype()), ns);
        if(simplified_typecast.is_constant())
        {
          floatbv_typecast_exprt new_floatbv_typecast_expr =
            floatbv_typecast_expr;
          new_floatbv_typecast_expr.op() = simplified_typecast;
          if(!simplify_floatbv_typecast(new_floatbv_typecast_expr))
          {
            expr = new_floatbv_typecast_expr;
            return false;
          }
        }
      }
    }
  }

  #if 0
  // (T)(a?b:c) --> a?(T)b:(T)c
  if(casted_expr.id()==ID_if)
  {
    auto const &casted_if_expr = to_if_expr(casted_expr);

    floatbv_typecast_exprt casted_true_case(casted_if_expr.true_case(), rounding_mode, dest_type);
    floatbv_typecast_exprt casted_false_case(casted_if_expr.false_case(), rounding_mode, dest_type);

    simplify_floatbv_typecast(casted_true_case);
    simplify_floatbv_typecast(casted_false_case);
    auto simplified_if_expr = simplify_expr(if_exprt(casted_if_expr.cond(), casted_true_case, casted_false_case, dest_type), ns);
    expr = simplified_if_expr;
    return false;
  }
  #endif

  return true;
}

bool simplify_exprt::simplify_floatbv_op(exprt &expr)
{
  const typet &type=ns.follow(expr.type());

  PRECONDITION(type.id() == ID_floatbv);
  PRECONDITION(
    expr.id() == ID_floatbv_plus || expr.id() == ID_floatbv_minus ||
    expr.id() == ID_floatbv_mult || expr.id() == ID_floatbv_div);
  DATA_INVARIANT(
    expr.operands().size() == 3,
    "binary operations have two operands, here an addtional parameter "
    "is for the rounding mode");

  exprt op0=expr.op0();
  exprt op1=expr.op1();
  exprt op2=expr.op2(); // rounding mode

  INVARIANT(
    ns.follow(op0.type()) == type,
    "expression type of operand must match type of expression");
  INVARIANT(
    ns.follow(op1.type()) == type,
    "expression type of operand must match type of expression");

  // Remember that floating-point addition is _NOT_ associative.
  // Thus, we don't re-sort the operands.
  // We only merge constants!

  if(op0.is_constant() && op1.is_constant() && op2.is_constant())
  {
    ieee_floatt v0(to_constant_expr(op0));
    ieee_floatt v1(to_constant_expr(op1));

    mp_integer rounding_mode;
    if(!to_integer(op2, rounding_mode))
    {
      v0.rounding_mode =
        (ieee_floatt::rounding_modet)numeric_cast_v<std::size_t>(rounding_mode);
      v1.rounding_mode=v0.rounding_mode;

      ieee_floatt result=v0;

      if(expr.id()==ID_floatbv_plus)
        result+=v1;
      else if(expr.id()==ID_floatbv_minus)
        result-=v1;
      else if(expr.id()==ID_floatbv_mult)
        result*=v1;
      else if(expr.id()==ID_floatbv_div)
        result/=v1;
      else
        UNREACHABLE;

      expr=result.to_expr();
      return false;
    }
  }

  // division by one? Exact for all rounding modes.
  if(expr.id()==ID_floatbv_div &&
     op1.is_constant() && op1.is_one())
  {
    exprt tmp;
    tmp.swap(op0);
    expr.swap(tmp);
    return false;
  }

  return true;
}

bool simplify_exprt::simplify_ieee_float_relation(exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_ieee_float_equal || expr.id() == ID_ieee_float_notequal);

  exprt::operandst &operands=expr.operands();

  if(expr.type().id()!=ID_bool)
    return true;

  if(operands.size()!=2)
    return true;

  // types must match
  if(expr.op0().type()!=expr.op1().type())
    return true;

  if(expr.op0().type().id()!=ID_floatbv)
    return true;

  // first see if we compare to a constant

  if(expr.op0().is_constant() &&
     expr.op1().is_constant())
  {
    ieee_floatt f0(to_constant_expr(expr.op0()));
    ieee_floatt f1(to_constant_expr(expr.op1()));

    if(expr.id()==ID_ieee_float_notequal)
      expr.make_bool(f0.ieee_not_equal(f1));
    else if(expr.id()==ID_ieee_float_equal)
      expr.make_bool(f0.ieee_equal(f1));
    else
      UNREACHABLE;

    return false;
  }

  if(expr.op0()==expr.op1())
  {
    // x!=x is the same as saying isnan(op)
    exprt isnan = isnan_exprt(expr.op0());

    if(expr.id()==ID_ieee_float_notequal)
    {
    }
    else if(expr.id()==ID_ieee_float_equal)
      isnan = not_exprt(isnan);
    else
      UNREACHABLE;

    expr.swap(isnan);
    return false;
  }

  return true;
}
