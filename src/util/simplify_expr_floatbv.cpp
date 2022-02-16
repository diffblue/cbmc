/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr_class.h"

#include "arith_tools.h"
#include "c_types.h"
#include "expr_util.h"
#include "floatbv_expr.h"
#include "ieee_float.h"
#include "invariant.h"
#include "namespace.h"
#include "simplify_expr.h"
#include "simplify_utils.h"
#include "std_expr.h"

simplify_exprt::resultt<>
simplify_exprt::simplify_isinf(const unary_exprt &expr)
{
  PRECONDITION(expr.op().type().id() == ID_floatbv);

  if(expr.op().is_constant())
  {
    ieee_floatt value(to_constant_expr(expr.op()));
    return make_boolean_expr(value.is_infinity());
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_isnan(const unary_exprt &expr)
{
  PRECONDITION(expr.op().type().id() == ID_floatbv);

  if(expr.op().is_constant())
  {
    ieee_floatt value(to_constant_expr(expr.op()));
    return make_boolean_expr(value.is_NaN());
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_isnormal(const unary_exprt &expr)
{
  PRECONDITION(expr.op().type().id() == ID_floatbv);

  if(expr.op().is_constant())
  {
    ieee_floatt value(to_constant_expr(expr.op()));
    return make_boolean_expr(value.is_normal());
  }

  return unchanged(expr);
}

#if 0
bool simplify_exprt::simplify_abs(exprt &expr)
{
  if(expr.operands().size()!=1)
    return true;

  if(expr.op0().is_constant())
  {
    const typet &type = expr.op0().type();

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
    const typet &type = expr.op0().type();

    if(type.id()==ID_floatbv)
    {
      ieee_floatt value(to_constant_expr(expr.op0()));
      expr = make_boolean_expr(value.get_sign());
      return false;
    }
    else if(type.id()==ID_signedbv ||
            type.id()==ID_unsignedbv)
    {
      mp_integer value;
      if(!to_integer(expr.op0(), value))
      {
        expr = make_boolean_expr(value>=0);
        return false;
      }
    }
  }

  return true;
}
#endif

simplify_exprt::resultt<>
simplify_exprt::simplify_floatbv_typecast(const floatbv_typecast_exprt &expr)
{
  // These casts usually reduce precision, and thus, usually round.

  const typet &dest_type = expr.type();
  const typet &src_type = expr.op().type();

  // eliminate redundant casts
  if(dest_type==src_type)
    return expr.op();

  const exprt &casted_expr = expr.op();
  const exprt &rounding_mode = expr.rounding_mode();

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
       casted_expr.op0().type()==dest_type &&
       casted_expr.op1().type()==dest_type)
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
    const auto rounding_mode_index = numeric_cast<mp_integer>(rounding_mode);
    if(rounding_mode_index.has_value())
    {
      if(src_type.id()==ID_floatbv)
      {
        if(dest_type.id()==ID_floatbv) // float to float
        {
          ieee_floatt result(to_constant_expr(casted_expr));
          result.rounding_mode =
            (ieee_floatt::rounding_modet)numeric_cast_v<std::size_t>(
              *rounding_mode_index);
          result.change_spec(
            ieee_float_spect(to_floatbv_type(dest_type)));
          return result.to_expr();
        }
        else if(dest_type.id()==ID_signedbv ||
                dest_type.id()==ID_unsignedbv)
        {
          if(*rounding_mode_index == ieee_floatt::ROUND_TO_ZERO)
          {
            ieee_floatt result(to_constant_expr(casted_expr));
            result.rounding_mode =
              (ieee_floatt::rounding_modet)numeric_cast_v<std::size_t>(
                *rounding_mode_index);
            mp_integer value=result.to_integer();
            return from_integer(value, dest_type);
          }
        }
      }
      else if(src_type.id()==ID_signedbv ||
              src_type.id()==ID_unsignedbv)
      {
        const auto value = numeric_cast<mp_integer>(casted_expr);
        if(value.has_value())
        {
          if(dest_type.id()==ID_floatbv) // int to float
          {
            ieee_floatt result(to_floatbv_type(dest_type));
            result.rounding_mode =
              (ieee_floatt::rounding_modet)numeric_cast_v<std::size_t>(
                *rounding_mode_index);
            result.from_integer(*value);
            return result.to_expr();
          }
        }
      }
      else if(src_type.id() == ID_c_enum_tag)
      {
        // go through underlying type
        const auto &enum_type = ns.follow_tag(to_c_enum_tag_type(src_type));
        exprt simplified_typecast = simplify_expr(
          typecast_exprt(casted_expr, enum_type.underlying_type()), ns);
        if(simplified_typecast.is_constant())
        {
          floatbv_typecast_exprt new_floatbv_typecast_expr = expr;
          new_floatbv_typecast_expr.op() = simplified_typecast;

          auto r = simplify_floatbv_typecast(new_floatbv_typecast_expr);

          if(r.has_changed())
            return r;
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

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_floatbv_op(const ieee_float_op_exprt &expr)
{
  const typet &type = expr.type();

  PRECONDITION(type.id() == ID_floatbv);
  PRECONDITION(
    expr.id() == ID_floatbv_plus || expr.id() == ID_floatbv_minus ||
    expr.id() == ID_floatbv_mult || expr.id() == ID_floatbv_div);

  const exprt &op0 = expr.lhs();
  const exprt &op1 = expr.rhs();
  const exprt &op2 = expr.rounding_mode();

  INVARIANT(
    op0.type() == type,
    "expression type of operand must match type of expression");
  INVARIANT(
    op1.type() == type,
    "expression type of operand must match type of expression");

  // Remember that floating-point addition is _NOT_ associative.
  // Thus, we don't re-sort the operands.
  // We only merge constants!

  if(op0.is_constant() && op1.is_constant() && op2.is_constant())
  {
    ieee_floatt v0(to_constant_expr(op0));
    ieee_floatt v1(to_constant_expr(op1));

    const auto rounding_mode = numeric_cast<mp_integer>(op2);
    if(rounding_mode.has_value())
    {
      v0.rounding_mode =
        (ieee_floatt::rounding_modet)numeric_cast_v<std::size_t>(
          *rounding_mode);
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

      return result.to_expr();
    }
  }

  // division by one? Exact for all rounding modes.
  if(expr.id()==ID_floatbv_div &&
     op1.is_constant() && op1.is_one())
  {
    return op0;
  }

  return unchanged(expr);
}

simplify_exprt::resultt<>
simplify_exprt::simplify_ieee_float_relation(const binary_relation_exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_ieee_float_equal || expr.id() == ID_ieee_float_notequal);

  // types must match
  if(expr.lhs().type() != expr.rhs().type())
    return unchanged(expr);

  if(expr.lhs().type().id() != ID_floatbv)
    return unchanged(expr);

  // first see if we compare to a constant

  if(expr.lhs().is_constant() && expr.rhs().is_constant())
  {
    ieee_floatt f_lhs(to_constant_expr(expr.lhs()));
    ieee_floatt f_rhs(to_constant_expr(expr.rhs()));

    if(expr.id()==ID_ieee_float_notequal)
      return make_boolean_expr(f_lhs.ieee_not_equal(f_rhs));
    else if(expr.id()==ID_ieee_float_equal)
      return make_boolean_expr(f_lhs.ieee_equal(f_rhs));
    else
      UNREACHABLE;
  }

  // addition and multiplication are commutative, but not associative
  exprt lhs_sorted = expr.lhs();
  if(lhs_sorted.id() == ID_floatbv_plus || lhs_sorted.id() == ID_floatbv_mult)
    sort_operands(lhs_sorted.operands());
  exprt rhs_sorted = expr.rhs();
  if(rhs_sorted.id() == ID_floatbv_plus || rhs_sorted.id() == ID_floatbv_mult)
    sort_operands(rhs_sorted.operands());

  if(lhs_sorted == rhs_sorted)
  {
    // x!=x is the same as saying isnan(op)
    exprt isnan = isnan_exprt(expr.lhs());

    if(expr.id()==ID_ieee_float_notequal)
    {
    }
    else if(expr.id()==ID_ieee_float_equal)
      isnan = not_exprt(isnan);
    else
      UNREACHABLE;

    return std::move(isnan);
  }

  return unchanged(expr);
}
