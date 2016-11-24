/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "simplify_expr_class.h"
#include "expr.h"
#include "namespace.h"
#include "ieee_float.h"
#include "std_expr.h"
#include "arith_tools.h"

/*******************************************************************\

Function: simplify_exprt::simplify_isinf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_isinf(exprt &expr)
{
  if(expr.operands().size()!=1) return true;

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

/*******************************************************************\

Function: simplify_exprt::simplify_isnan

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_isnan(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
 
  if(expr.op0().is_constant())
  {
    ieee_floatt value(to_constant_expr(expr.op0()));
    expr.make_bool(value.is_NaN());
    return false;
  }
  
  return true; 
}

/*******************************************************************\

Function: simplify_exprt::simplify_isnormal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_isnormal(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
 
  if(expr.op0().is_constant())
  {
    ieee_floatt value(to_constant_expr(expr.op0()));
    expr.make_bool(value.is_normal());
    return false;
  }
  
  return true; 
}

/*******************************************************************\

Function: simplify_exprt::simplify_abs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
bool simplify_exprt::simplify_abs(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
 
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

/*******************************************************************\

Function: simplify_exprt::simplify_sign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
bool simplify_exprt::simplify_sign(exprt &expr)
{
  if(expr.operands().size()!=1) return true;
 
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

/*******************************************************************\

Function: simplify_exprt::simplify_floatbv_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_floatbv_typecast(exprt &expr)
{
  // These casts usually reduce precision, and thus, usually round.
  
  assert(expr.operands().size()==2);
        
  const typet &dest_type=ns.follow(expr.type());
  const typet &src_type=ns.follow(expr.op0().type());

  // eliminate redundant casts
  if(dest_type==src_type)
  {
    expr=expr.op0();
    return false;
  }
  
  exprt op0=expr.op0();
  exprt op1=expr.op1(); // rounding mode
  
  // We can soundly re-write (float)((double)x op (double)y)
  // to x op y. True for any rounding mode!

  #if 0
  if(op0.id()==ID_floatbv_div ||
     op0.id()==ID_floatbv_mult ||
     op0.id()==ID_floatbv_plus ||
     op0.id()==ID_floatbv_minus)
  {
    if(op0.operands().size()==3 &&
       op0.op0().id()==ID_typecast &&
       op0.op1().id()==ID_typecast &&
       op0.op0().operands().size()==1 &&
       op0.op1().operands().size()==1 &&
       ns.follow(op0.op0().type())==dest_type &&
       ns.follow(op0.op1().type())==dest_type)
    {
      exprt result(op0.id(), expr.type());
      result.operands().resize(3);
      result.op0()=op0.op0().op0();
      result.op1()=op0.op1().op0();
      result.op2()=op1;

      simplify_node(result);
      expr.swap(result);
      return false;
    }
  }
  #endif

  // constant folding  
  if(op0.is_constant() && op1.is_constant())
  {
    mp_integer rounding_mode;
    if(!to_integer(op1, rounding_mode))
    {
      if(src_type.id()==ID_floatbv)
      {
        if(dest_type.id()==ID_floatbv) // float to float
        {
          ieee_floatt result(to_constant_expr(op0));
          result.rounding_mode=(ieee_floatt::rounding_modet)integer2long(rounding_mode);
          result.change_spec(to_floatbv_type(dest_type));
          expr=result.to_expr();
          return false;
        }
        else if(dest_type.id()==ID_signedbv ||
                dest_type.id()==ID_unsignedbv)
        {
          if(rounding_mode==ieee_floatt::ROUND_TO_ZERO)
          {
            ieee_floatt result(to_constant_expr(op0));
            result.rounding_mode=(ieee_floatt::rounding_modet)integer2long(rounding_mode);
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
        if(!to_integer(op0, value))
        {
          if(dest_type.id()==ID_floatbv) // int to float
          {
            ieee_floatt result;
            result.rounding_mode=(ieee_floatt::rounding_modet)integer2long(rounding_mode);
            result.spec=to_floatbv_type(dest_type);
            result.from_integer(value);
            expr=result.to_expr();
            return false;
          }
        }
      }
    }
  }

  #if 0
  // (T)(a?b:c) --> a?(T)b:(T)c
  if(expr.op0().id()==ID_if &&
     expr.op0().operands().size()==3)
  {
    exprt tmp_op1=binary_exprt(expr.op0().op1(), ID_floatbv_typecast, expr.op1(), dest_type);
    exprt tmp_op2=binary_exprt(expr.op0().op2(), ID_floatbv_typecast, expr.op1(), dest_type);
    simplify_floatbv_typecast(tmp_op1);
    simplify_floatbv_typecast(tmp_op2);
    expr=if_exprt(expr.op0().op0(), tmp_op1, tmp_op2, dest_type);
    simplify_if(expr);
    return false;
  }
  #endif
  
  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_floatbv_op

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_floatbv_op(exprt &expr)
{
  const typet &type=ns.follow(expr.type());
  
  if(type.id()!=ID_floatbv)
    return true;

  assert(expr.operands().size()==3);
  
  exprt op0=expr.op0();
  exprt op1=expr.op1();
  exprt op2=expr.op2(); // rounding mode

  assert(ns.follow(op0.type())==type);
  assert(ns.follow(op1.type())==type);

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
      v0.rounding_mode=(ieee_floatt::rounding_modet)integer2long(rounding_mode);
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
        assert(false);

      expr=result.to_expr();
      return false;
    }
  }

  // division by one? Exact for all rounding modes.
  if (expr.id()==ID_floatbv_div &&
      op1.is_constant() && op1.is_one())
  { 
    exprt tmp;
    tmp.swap(op0);
    expr.swap(tmp);
    return false;
  }
  
  return true;
}

/*******************************************************************\

Function: simplify_exprt::simplify_ieee_float_relation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simplify_exprt::simplify_ieee_float_relation(exprt &expr)
{
  assert(expr.id()==ID_ieee_float_equal ||
         expr.id()==ID_ieee_float_notequal);

  exprt::operandst &operands=expr.operands();

  if(expr.type().id()!=ID_bool) return true;

  if(operands.size()!=2) return true;

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
      expr.make_bool(ieee_not_equal(f0, f1));
    else if(expr.id()==ID_ieee_float_equal)
      expr.make_bool(ieee_equal(f0, f1));
    else
      assert(false);
  
    return false;
  }

  if(expr.op0()==expr.op1())
  {
    // x!=x is the same as saying isnan(op)
    exprt isnan(ID_isnan, bool_typet());
    isnan.copy_to_operands(expr.op0());

    if(expr.id()==ID_ieee_float_notequal)
    {
    }
    else if(expr.id()==ID_ieee_float_equal)
      isnan.make_not();
    else
      assert(false);
  
    expr.swap(isnan);
    return false;
  }

  return true;
}

