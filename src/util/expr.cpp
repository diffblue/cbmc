/*******************************************************************\

Module: Expression Representation

Author: Daniel Kroening, kroening@kroening.com
        Joel Allred, joel.allred@diffblue.com

\*******************************************************************/

/// \file
/// Expression Representation

// clang-format off
#include "arith_tools.h"
#include "expr.h"
#include "expr_iterator.h"
#include "fixedbv.h"
#include "ieee_float.h"
#include "rational.h"
#include "rational_tools.h"
#include "std_expr.h"
// clang-format on

#include <stack>

/// Move the given argument to the end of `exprt`'s operands.
/// The argument is destroyed and mutated to a reference to a nil `irept`.
/// \param expr: `exprt` to append to the operands
void exprt::move_to_operands(exprt &expr)
{
  operandst &op=operands();
  op.push_back(static_cast<const exprt &>(get_nil_irep()));
  op.back().swap(expr);
}

/// Move the given arguments to the end of `exprt`'s operands.
/// The arguments are destroyed and mutated to a reference to a nil `irept`.
/// \param e1: first `exprt` to append to the operands
/// \param e2: second `exprt` to append to the operands
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

/// Move the given arguments to the end of `exprt`'s operands.
/// The arguments are destroyed and mutated to a reference to a nil `irept`.
/// \param e1: first `exprt` to append to the operands
/// \param e2: second `exprt` to append to the operands
/// \param e3: third `exprt` to append to the operands
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

/// Create a \ref typecast_exprt to the given type.
/// \param _type: cast destination type
/// \deprecated use constructors instead
void exprt::make_typecast(const typet &_type)
{
  typecast_exprt new_expr(*this, _type);

  swap(new_expr);
}

/// Negate the expression.
/// Simplifications:
///   - If the expression is trivially true, make it false, and vice versa.
///   - If the expression is an `ID_not`, remove the not.
/// \deprecated use constructors instead
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
    new_expr = not_exprt(*this);
  }

  swap(new_expr);
}

/// Return whether the expression is a constant.
/// \return True if is a constant, false otherwise
bool exprt::is_constant() const
{
  return id()==ID_constant;
}

/// Return whether the expression is a constant representing `true`.
/// \return True if is a Boolean constant representing `true`, false otherwise.
bool exprt::is_true() const
{
  return is_constant() &&
         type().id()==ID_bool &&
         get(ID_value)!=ID_false;
}

/// Return whether the expression is a constant representing `false`.
/// \return True if is a Boolean constant representing `false`, false otherwise.
bool exprt::is_false() const
{
  return is_constant() &&
         type().id()==ID_bool &&
         get(ID_value)==ID_false;
}

/// Replace the expression by a Boolean expression representing \p value.
/// \param value: the Boolean value to give to the expression
/// \deprecated use constructors instead
void exprt::make_bool(bool value)
{
  *this=exprt(ID_constant, typet(ID_bool));
  set(ID_value, value?ID_true:ID_false);
}

/// Replace the expression by a Boolean expression representing true.
/// \deprecated use constructors instead
void exprt::make_true()
{
  *this=exprt(ID_constant, typet(ID_bool));
  set(ID_value, ID_true);
}

/// Replace the expression by a Boolean expression representing false.
/// \deprecated use constructors instead
void exprt::make_false()
{
  *this=exprt(ID_constant, typet(ID_bool));
  set(ID_value, ID_false);
}

/// Return whether the expression represents a Boolean.
/// \return True if is a Boolean, false otherwise.
bool exprt::is_boolean() const
{
  return type().id()==ID_bool;
}

/// Return whether the expression is a constant representing 0.
/// Will consider the following types: ID_integer, ID_natural, ID_rational,
/// ID_unsignedbv, ID_signedbv, ID_c_bool, ID_c_bit_field, ID_fixedbv,
/// ID_floatbv, ID_pointer.<br>
/// For ID_pointer, returns true iff the value is a zero string or a null
/// pointer.
/// For everything not in the above list, return false.
/// \return True if has value 0, false otherwise.
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
    else if(
      type_id == ID_unsignedbv || type_id == ID_signedbv ||
      type_id == ID_c_bool || type_id == ID_c_bit_field)
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

/// Return whether the expression is a constant representing 1.
/// Will consider the following types: ID_integer, ID_natural, ID_rational,
/// ID_unsignedbv, ID_signedbv, ID_c_bool, ID_c_bit_field, ID_fixedbv,
/// ID_floatbv.<br>
/// For all other types, return false.
/// \return True if has value 1, false otherwise.
bool exprt::is_one() const
{
  if(is_constant())
  {
    const auto &constant_expr = to_constant_expr(*this);
    const irep_idt &type_id = type().id();

    if(type_id==ID_integer || type_id==ID_natural)
    {
      mp_integer int_value =
        string2integer(id2string(constant_expr.get_value()));
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
      const auto width = to_bitvector_type(type()).get_width();
      mp_integer int_value =
        bvrep2integer(id2string(constant_expr.get_value()), width, false);
      if(int_value==1)
        return true;
    }
    else if(type_id==ID_fixedbv)
    {
      if(fixedbvt(constant_expr) == 1)
        return true;
    }
    else if(type_id==ID_floatbv)
    {
      if(ieee_floatt(constant_expr) == 1)
        return true;
    }
  }

  return false;
}

/// Get a \ref source_locationt from the expression or from its operands
/// (non-recursively).
/// If no source location is found, a nil `source_locationt` is returned.
/// \return A source location if found in the expression or its operands, nil
/// otherwise.
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
