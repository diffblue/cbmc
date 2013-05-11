/*******************************************************************\

Module: Expression Representation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <cassert>

#include <stack>

#include "mp_arith.h"
#include "fixedbv.h"
#include "ieee_float.h"
#include "expr.h"
#include "rational.h"
#include "rational_tools.h"
#include "arith_tools.h"
#include "std_expr.h"

/*******************************************************************\

Function: exprt::move_to_operands

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void exprt::move_to_operands(exprt &expr)
{
  operandst &op=operands();
  op.push_back(static_cast<const exprt &>(get_nil_irep()));
  op.back().swap(expr);
}

/*******************************************************************\

Function: exprt::move_to_operands

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void exprt::move_to_operands(exprt &e1, exprt &e2)
{
  operandst &op=operands();
  #ifndef USE_LIST
  op.reserve(op.size()+2);
  #endif
  op.push_back(static_cast<const exprt &>(get_nil_irep()));
  op.back().swap(e1);
  op.push_back(static_cast<const exprt &>(get_nil_irep()));
  op.back().swap(e2);
}

/*******************************************************************\

Function: exprt::move_to_operands

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void exprt::move_to_operands(exprt &e1, exprt &e2, exprt &e3)
{
  operandst &op=operands();
  #ifndef USE_LIST
  op.reserve(op.size()+3);
  #endif
  op.push_back(static_cast<const exprt &>(get_nil_irep()));
  op.back().swap(e1);
  op.push_back(static_cast<const exprt &>(get_nil_irep()));
  op.back().swap(e2);
  op.push_back(static_cast<const exprt &>(get_nil_irep()));
  op.back().swap(e3);
}

/*******************************************************************\

Function: exprt::copy_to_operands

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void exprt::copy_to_operands(const exprt &expr)
{
  operands().push_back(expr);
}

/*******************************************************************\

Function: exprt::copy_to_operands

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void exprt::copy_to_operands(const exprt &e1, const exprt &e2)
{
  operandst &op=operands();
  #ifndef USE_LIST
  op.reserve(op.size()+2);
  #endif
  op.push_back(e1);
  op.push_back(e2);
}

/*******************************************************************\

Function: exprt::copy_to_operands

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void exprt::copy_to_operands(const exprt &e1, const exprt &e2,
                             const exprt &e3)
{
  operandst &op=operands();
  #ifndef USE_LIST
  op.reserve(op.size()+3);
  #endif
  op.push_back(e1);
  op.push_back(e2);
  op.push_back(e3);
}

/*******************************************************************\

Function: exprt::make_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void exprt::make_typecast(const typet &_type)
{
  exprt new_expr(ID_typecast);

  new_expr.move_to_operands(*this);
  new_expr.set(ID_type, _type);

  swap(new_expr);
}

/*******************************************************************\

Function: exprt::make_not

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void exprt::make_not()
{
  if(is_true())
  {
    make_false();
    return;
  }
  else if(is_false())
  {
    make_true();
    return;
  }

  exprt new_expr;

  if(id()==ID_not && operands().size()==1)
  {
    new_expr.swap(operands().front());
  }
  else
  {
    new_expr=exprt(ID_not, type());
    new_expr.move_to_operands(*this);
  }

  swap(new_expr);
}

/*******************************************************************\

Function: exprt::is_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool exprt::is_constant() const
{
  return id()==ID_constant;
}

/*******************************************************************\

Function: exprt::is_true

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool exprt::is_true() const
{
  return is_constant() &&
         type().id()==ID_bool &&
         get(ID_value)!=ID_false;
}

/*******************************************************************\

Function: exprt::is_false

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool exprt::is_false() const
{
  return is_constant() &&
         type().id()==ID_bool &&
         get(ID_value)==ID_false;
}

/*******************************************************************\

Function: exprt::make_bool

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void exprt::make_bool(bool value)
{
  *this=exprt(ID_constant, typet(ID_bool));
  set(ID_value, value?ID_true:ID_false);
}

/*******************************************************************\

Function: exprt::make_true

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void exprt::make_true()
{
  *this=exprt(ID_constant, typet(ID_bool));
  set(ID_value, ID_true);
}

/*******************************************************************\

Function: exprt::make_false

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void exprt::make_false()
{
  *this=exprt(ID_constant, typet(ID_bool));
  set(ID_value, ID_false);
}

/*******************************************************************\

Function: operator<

  Inputs:

 Outputs:

 Purpose: defines ordering on expressions for canonicalization

\*******************************************************************/

bool operator<(const exprt &X, const exprt &Y)
{
  return (irept &)X < (irept &)Y;
}

/*******************************************************************\

Function: exprt::negate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void exprt::negate()
{
  const irep_idt &type_id=type().id();

  if(type_id==ID_bool)
    make_not();
  else
  {
    if(is_constant())
    {
      const irep_idt &value=get(ID_value);
      
      if(type_id==ID_integer)
      {
        set(ID_value, integer2string(-string2integer(id2string(value))));
      }
      else if(type_id==ID_unsignedbv)
      {
        mp_integer int_value=binary2integer(id2string(value), false);
        typet _type=type();
        *this=from_integer(-int_value, _type);
      }
      else if(type_id==ID_signedbv)
      {
        mp_integer int_value=binary2integer(id2string(value), true);
        typet _type=type();
        *this=from_integer(-int_value, _type);
      }
      else if(type_id==ID_fixedbv)
      {
        fixedbvt fixedbv_value=fixedbvt(to_constant_expr(*this));
        fixedbv_value.negate();
        *this=fixedbv_value.to_expr();
      }
      else if(type_id==ID_floatbv)
      {
        ieee_floatt ieee_float_value=ieee_floatt(to_constant_expr(*this));
        ieee_float_value.negate();
        *this=ieee_float_value.to_expr();
      }
      else
      {
        make_nil();
        assert(false);
      }
    }
    else
    {
      if(id()==ID_unary_minus)
      {
        exprt tmp;
        assert(operands().size()==1);
        tmp.swap(op0());
        swap(tmp);
      }
      else
      {
        exprt tmp(ID_unary_minus, type());
        tmp.move_to_operands(*this);
        swap(tmp);
      }
    }
  }
}

/*******************************************************************\

Function: exprt::is_boolean

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool exprt::is_boolean() const
{
  return type().id()==ID_bool;
}

/*******************************************************************\

Function: exprt::is_zero

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool exprt::is_zero() const
{
  if(is_constant())
  {
    const irep_idt value=get_string(ID_value);
    const irep_idt &type_id=type().id_string();

    if(type_id==ID_integer || type_id==ID_natural)
    {
      mp_integer int_value=string2integer(id2string(value));
      if(int_value==0) return true;
    }
    else if(type_id==ID_rational)
    {
      rationalt rat_value;
      if(to_rational(*this, rat_value)) assert(false);
      return rat_value.is_zero();
    }
    else if(type_id==ID_unsignedbv || type_id==ID_signedbv)
    {
      mp_integer int_value=binary2integer(id2string(value), false);
      if(int_value==0) return true;
    }
    else if(type_id==ID_fixedbv)
    {
      if(fixedbvt(to_constant_expr(*this))==0) return true;
    }
    else if(type_id==ID_floatbv)
    {
      if(ieee_floatt(to_constant_expr(*this))==0) return true;
    }
    else if(type_id==ID_pointer)
    {
      if(value==ID_NULL) return true;
      mp_integer int_value=binary2integer(id2string(value), false);
      if(int_value==0) return true;
    }
  }

  return false;
}

/*******************************************************************\

Function: exprt::is_one

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool exprt::is_one() const
{
  if(is_constant())
  {
    const std::string &value=get_string(ID_value);
    const irep_idt &type_id=type().id_string();

    if(type_id==ID_integer || type_id==ID_natural)
    {
      mp_integer int_value=string2integer(value);
      if(int_value==1) return true;
    }
    else if(type_id==ID_rational)
    {
      rationalt rat_value;
      if(to_rational(*this, rat_value)) assert(false);
      return rat_value.is_one();
    }
    else if(type_id==ID_unsignedbv || type_id==ID_signedbv)
    {
      mp_integer int_value=binary2integer(value, false);
      if(int_value==1) return true;
    }
    else if(type_id==ID_fixedbv)
    {
      if(fixedbvt(to_constant_expr(*this))==1)
        return true;
    }
    else if(type_id==ID_floatbv)
    {
      if(ieee_floatt(to_constant_expr(*this))==1)
        return true;
    }
  }

  return false;
}

/*******************************************************************\

Function: exprt::sum

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool exprt::sum(const exprt &expr)
{
  if(!is_constant() || !expr.is_constant()) return true;
  if(type()!=expr.type()) return true;

  const irep_idt &type_id=type().id();

  if(type_id==ID_integer || type_id==ID_natural)
  {
    set(ID_value, integer2string(
      string2integer(get_string(ID_value))+
      string2integer(expr.get_string(ID_value))));
    return false;
  }
  else if(type_id==ID_rational)
  {
    rationalt a, b;
    if(!to_rational(*this, a) && !to_rational(expr, b))
    {
      exprt a_plus_b=from_rational(a+b);
      set(ID_value, a_plus_b.get_string(ID_value));
      return false;
    }
  }
  else if(type_id==ID_unsignedbv || type_id==ID_signedbv)
  {
    set(ID_value, integer2binary(
      binary2integer(get_string(ID_value), false)+
      binary2integer(expr.get_string(ID_value), false),
      atoi(type().get(ID_width).c_str())));
    return false;
  }
  else if(type_id==ID_fixedbv)
  {
    set(ID_value, integer2binary(
      binary2integer(get_string(ID_value), false)+
      binary2integer(expr.get_string(ID_value), false),
      atoi(type().get(ID_width).c_str())));
    return false;
  }
  else if(type_id==ID_floatbv)
  {
    ieee_floatt f(to_constant_expr(*this));
    f+=ieee_floatt(to_constant_expr(expr));
    *this=f.to_expr();
    return false;
  }

  return true;
}

/*******************************************************************\

Function: exprt::mul

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool exprt::mul(const exprt &expr)
{
  if(!is_constant() || !expr.is_constant()) return true;
  if(type()!=expr.type()) return true;

  const irep_idt &type_id=type().id();

  if(type_id==ID_integer || type_id==ID_natural)
  {
    set(ID_value, integer2string(
      string2integer(get_string(ID_value))*
      string2integer(expr.get_string(ID_value))));
    return false;
  }
  else if(type_id==ID_rational)
  {
    rationalt a, b;
    if(!to_rational(*this, a) && !to_rational(expr, b))
    {
      exprt a_mul_b=from_rational(a*b);
      set(ID_value, a_mul_b.get_string(ID_value));
      return false;
    }
  }
  else if(type_id==ID_unsignedbv || type_id==ID_signedbv)
  {
    // the following works for signed and unsigned integers
    set(ID_value, integer2binary(
      binary2integer(get_string(ID_value), false)*
      binary2integer(expr.get_string(ID_value), false),
      atoi(type().get(ID_width).c_str())));
    return false;
  }
  else if(type_id==ID_fixedbv)
  {
    fixedbvt f(to_constant_expr(*this));
    f*=fixedbvt(to_constant_expr(expr));
    *this=f.to_expr();
    return false;
  }
  else if(type_id==ID_floatbv)
  {
    ieee_floatt f(to_constant_expr(*this));
    f*=ieee_floatt(to_constant_expr(expr));
    *this=f.to_expr();
    return false;
  }

  return true;
}

/*******************************************************************\

Function: exprt::subtract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool exprt::subtract(const exprt &expr)
{
  if(!is_constant() || !expr.is_constant()) return true;

  if(type()!=expr.type()) return true;

  const irep_idt &type_id=type().id();

  if(type_id==ID_integer || type_id==ID_natural)
  {
    set(ID_value, integer2string(
      string2integer(get_string(ID_value))-
      string2integer(expr.get_string(ID_value))));
    return false;
  }
  else if(type_id==ID_rational)
  {
    rationalt a, b;
    if(!to_rational(*this, a) && !to_rational(expr, b))
    {
      exprt a_minus_b=from_rational(a-b);
      set(ID_value, a_minus_b.get_string(ID_value));
      return false;
    }
  }
  else if(type_id==ID_unsignedbv || type_id==ID_signedbv)
  {
    set(ID_value, integer2binary(
      binary2integer(get_string(ID_value), false)-
      binary2integer(expr.get_string(ID_value), false),
      atoi(type().get(ID_width).c_str())));
    return false;
  }

  return true;
}

/*******************************************************************\

Function: exprt::find_location

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const locationt &exprt::find_location() const
{
  const locationt &l=location();

  if(l.is_not_nil()) return l;

  forall_operands(it, (*this))
  {
    const locationt &l=it->find_location();
    if(l.is_not_nil()) return l;
  }

  return static_cast<const locationt &>(get_nil_irep());
}

/*******************************************************************\

Function: exprt::visit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void exprt::visit(expr_visitort &visitor)
{
  std::stack<exprt *> stack;
  
  stack.push(this);

  while(!stack.empty())
  {
    exprt &expr=*stack.top();
    stack.pop();

    visitor(expr);

    Forall_operands(it, expr)
      stack.push(&(*it));
  }
}

/*******************************************************************\

Function: exprt::visit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void exprt::visit(const_expr_visitort &visitor) const
{
  std::stack<const exprt *> stack;
  
  stack.push(this);

  while(!stack.empty())
  {
    const exprt &expr=*stack.top();
    stack.pop();

    visitor(expr);

    forall_operands(it, expr)
      stack.push(&(*it));
  }
}
