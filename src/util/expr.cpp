/*******************************************************************\

Module: Expression Representation

Author: Daniel Kroening, kroening@kroening.com
        Joel Allred, joel.allred@diffblue.com

\*******************************************************************/

/// \file
/// Expression Representation

#include "arith_tools.h"
#include "bitvector_types.h"
#include "expr_iterator.h"
#include "fixedbv.h"
#include "ieee_float.h"
#include "rational.h"
#include "rational_tools.h"
#include "std_expr.h"

#include <stack>

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
    else if(
      type_id == ID_unsignedbv || type_id == ID_signedbv ||
      type_id == ID_c_bool || type_id == ID_c_bit_field)
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
///   otherwise.
const source_locationt &exprt::find_source_location() const
{
  const source_locationt &l=source_location();

  if(l.is_not_nil())
    return l;

  forall_operands(it, (*this))
  {
    const source_locationt &op_l = it->find_source_location();
    if(op_l.is_not_nil())
      return op_l;
  }

  return source_locationt::nil();
}

template <typename T>
void visit_post_template(std::function<void(T &)> visitor, T *_expr)
{
  struct stack_entryt
  {
    T *e;
    bool operands_pushed;
    explicit stack_entryt(T *_e) : e(_e), operands_pushed(false)
    {
    }
  };

  std::stack<stack_entryt> stack;

  stack.emplace(_expr);

  while(!stack.empty())
  {
    auto &top = stack.top();
    if(top.operands_pushed)
    {
      visitor(*top.e);
      stack.pop();
    }
    else
    {
      // do modification of 'top' before pushing in case 'top' isn't stable
      top.operands_pushed = true;
      for(auto &op : top.e->operands())
        stack.emplace(&op);
    }
  }
}

void exprt::visit_post(std::function<void(exprt &)> visitor)
{
  visit_post_template(visitor, this);
}

void exprt::visit_post(std::function<void(const exprt &)> visitor) const
{
  visit_post_template(visitor, this);
}

template <typename T>
static void visit_pre_template(std::function<void(T &)> visitor, T *_expr)
{
  std::stack<T *> stack;

  stack.push(_expr);

  while(!stack.empty())
  {
    T &expr = *stack.top();
    stack.pop();

    visitor(expr);

    for(auto &op : expr.operands())
      stack.push(&op);
  }
}

void exprt::visit_pre(std::function<void(exprt &)> visitor)
{
  visit_pre_template(visitor, this);
}

void exprt::visit_pre(std::function<void(const exprt &)> visitor) const
{
  visit_pre_template(visitor, this);
}

void exprt::visit(expr_visitort &visitor)
{
  visit_pre([&visitor](exprt &e) { visitor(e); });
}

void exprt::visit(const_expr_visitort &visitor) const
{
  visit_pre([&visitor](const exprt &e) { visitor(e); });
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
