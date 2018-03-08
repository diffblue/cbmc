/*******************************************************************\

Module: Expression Representation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Expression Representation

#include "expr.h"
#include "expr_iterator.h"
#include "fixedbv.h"
#include "ieee_float.h"
#include "rational.h"
#include "rational_tools.h"
#include "std_expr.h"

#include <stack>

void exprt::move_to_operands(exprt &expr)
{
  operandst &op=operands();
  op.push_back(static_cast<const exprt &>(get_nil_irep()));
  op.back().swap(expr);
}

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

void exprt::copy_to_operands(const exprt &expr)
{
  operands().push_back(expr);
}

void exprt::copy_to_operands(const exprt &e1, const exprt &e2)
{
  operandst &op=operands();
  #ifndef USE_LIST
  op.reserve(op.size()+2);
  #endif
  op.push_back(e1);
  op.push_back(e2);
}

void exprt::copy_to_operands(
  const exprt &e1,
  const exprt &e2,
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

void exprt::make_typecast(const typet &_type)
{
  typecast_exprt new_expr(*this, _type);

  swap(new_expr);
}

void exprt::make_not()
{
  if(is_true())
  {
    *this=false_exprt();
    return;
  }
  else if(is_false())
  {
    *this=true_exprt();
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

bool exprt::is_constant() const
{
  return id()==ID_constant;
}

bool exprt::is_true() const
{
  return is_constant() &&
         type().id()==ID_bool &&
         get(ID_value)!=ID_false;
}

bool exprt::is_false() const
{
  return is_constant() &&
         type().id()==ID_bool &&
         get(ID_value)==ID_false;
}

void exprt::make_bool(bool value)
{
  *this=exprt(ID_constant, typet(ID_bool));
  set(ID_value, value?ID_true:ID_false);
}

void exprt::make_true()
{
  *this=exprt(ID_constant, typet(ID_bool));
  set(ID_value, ID_true);
}

void exprt::make_false()
{
  *this=exprt(ID_constant, typet(ID_bool));
  set(ID_value, ID_false);
}

bool exprt::is_boolean() const
{
  return type().id()==ID_bool;
}

bool exprt::is_zero() const
{
  if(is_constant())
  {
    const constant_exprt &constant=to_constant_expr(*this);
    const irep_idt &type_id=type().id_string();

    if(type_id==ID_integer || type_id==ID_natural)
    {
      return constant.value_is_zero_string();
    }
    else if(type_id==ID_rational)
    {
      rationalt rat_value;
      if(to_rational(*this, rat_value))
        CHECK_RETURN(false);
      return rat_value.is_zero();
    }
    else if(type_id==ID_unsignedbv ||
            type_id==ID_signedbv ||
            type_id==ID_c_bool)
    {
      return constant.value_is_zero_string();
    }
    else if(type_id==ID_fixedbv)
    {
      if(fixedbvt(constant)==0)
        return true;
    }
    else if(type_id==ID_floatbv)
    {
      if(ieee_floatt(constant)==0)
        return true;
    }
    else if(type_id==ID_pointer)
    {
      return constant.value_is_zero_string() ||
             constant.get_value()==ID_NULL;
    }
  }

  return false;
}

bool exprt::is_one() const
{
  if(is_constant())
  {
    const std::string &value=get_string(ID_value);
    const irep_idt &type_id=type().id_string();

    if(type_id==ID_integer || type_id==ID_natural)
    {
      mp_integer int_value=string2integer(value);
      if(int_value==1)
        return true;
    }
    else if(type_id==ID_rational)
    {
      rationalt rat_value;
      if(to_rational(*this, rat_value))
        CHECK_RETURN(false);
      return rat_value.is_one();
    }
    else if(type_id==ID_unsignedbv || type_id==ID_signedbv)
    {
      mp_integer int_value=binary2integer(value, false);
      if(int_value==1)
        return true;
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

const source_locationt &exprt::find_source_location() const
{
  const source_locationt &l=source_location();

  if(l.is_not_nil())
    return l;

  forall_operands(it, (*this))
  {
    const source_locationt &l=it->find_source_location();
    if(l.is_not_nil())
      return l;
  }

  return static_cast<const source_locationt &>(get_nil_irep());
}

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

depth_iteratort exprt::depth_begin()
{ return depth_iteratort(*this); }
depth_iteratort exprt::depth_end()
{ return depth_iteratort(); }
const_depth_iteratort exprt::depth_begin() const
{ return const_depth_iteratort(*this); }
const_depth_iteratort exprt::depth_end() const
{ return const_depth_iteratort(); }
const_depth_iteratort exprt::depth_cbegin() const
{ return const_depth_iteratort(*this); }
const_depth_iteratort exprt::depth_cend() const
{ return const_depth_iteratort(); }
depth_iteratort exprt::depth_begin(std::function<exprt &()> mutate_root) const
{
  return depth_iteratort(*this, std::move(mutate_root));
}

const_unique_depth_iteratort exprt::unique_depth_begin() const
{ return const_unique_depth_iteratort(*this); }
const_unique_depth_iteratort exprt::unique_depth_end() const
{ return const_unique_depth_iteratort(); }
const_unique_depth_iteratort exprt::unique_depth_cbegin() const
{ return const_unique_depth_iteratort(*this); }
const_unique_depth_iteratort exprt::unique_depth_cend() const
{ return const_unique_depth_iteratort(); }
