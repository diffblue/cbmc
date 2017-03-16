/******************************************************************\

Module: String expressions for the string solver

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// String expressions for the string solver

#ifndef CPROVER_UTIL_STRING_EXPR_H
#define CPROVER_UTIL_STRING_EXPR_H

#include <util/std_expr.h>
#include <util/arith_tools.h>

class string_exprt: public struct_exprt
{
public:
  string_exprt(): struct_exprt() {}

  explicit string_exprt(typet type): struct_exprt(type)
  {
    operands().resize(2);
  }

  string_exprt(const exprt &_length, const exprt &_content, typet type):
    struct_exprt(type)
  {
    copy_to_operands(_length, _content);
  }

  // Expression corresponding to the length of the string
  const exprt &length() const { return op0(); }
  exprt &length() { return op0(); }

  // Expression corresponding to the content (array of characters) of the string
  const exprt &content() const { return op1(); }
  exprt &content() { return op1(); }

  static exprt within_bounds(const exprt &idx, const exprt &bound);

  // Expression of the character at position idx in the string
  index_exprt operator[] (const exprt &idx) const
  {
    return index_exprt(content(), idx);
  }

  index_exprt operator[] (int i) const
  {
    return index_exprt(content(), from_integer(i, length().type()));
  }

  // Comparison on the length of the strings
  binary_relation_exprt axiom_for_is_longer_than(
    const string_exprt &rhs) const
  {
    return binary_relation_exprt(length(), ID_ge, rhs.length());
  }

  binary_relation_exprt axiom_for_is_longer_than(
    const exprt &rhs) const
  {
    return binary_relation_exprt(length(), ID_ge, rhs);
  }

  binary_relation_exprt axiom_for_is_strictly_longer_than(
    const exprt &rhs) const
  {
    return binary_relation_exprt(rhs, ID_lt, length());
  }

  binary_relation_exprt axiom_for_is_strictly_longer_than(
    const string_exprt &rhs) const
  {
    return binary_relation_exprt(rhs.length(), ID_lt, length());
  }

  binary_relation_exprt axiom_for_is_strictly_longer_than(mp_integer i) const
  {
    return axiom_for_is_strictly_longer_than(from_integer(i, length().type()));
  }

  binary_relation_exprt axiom_for_is_shorter_than(
    const string_exprt &rhs) const
  {
    return binary_relation_exprt(length(), ID_le, rhs.length());
  }

  binary_relation_exprt axiom_for_is_shorter_than(
    const exprt &rhs) const
  {
    return binary_relation_exprt(length(), ID_le, rhs);
  }

  binary_relation_exprt axiom_for_is_shorter_than(mp_integer i) const
  {
    return axiom_for_is_shorter_than(from_integer(i, length().type()));
  }

  binary_relation_exprt axiom_for_is_strictly_shorter_than(
    const string_exprt &rhs) const
  {
    return binary_relation_exprt(length(), ID_lt, rhs.length());
  }

  binary_relation_exprt axiom_for_is_strictly_shorter_than(
    const exprt &rhs) const
  {
    return binary_relation_exprt(length(), ID_lt, rhs);
  }

  equal_exprt axiom_for_has_same_length_as(
    const string_exprt &rhs) const
  {
    return equal_exprt(length(), rhs.length());
  }

  equal_exprt axiom_for_has_length(const exprt &rhs) const
  {
    return equal_exprt(length(), rhs);
  }

  equal_exprt axiom_for_has_length(mp_integer i) const
  {
    return axiom_for_has_length(from_integer(i, length().type()));
  }

  friend inline string_exprt &to_string_expr(exprt &expr);
};

inline string_exprt &to_string_expr(exprt &expr)
{
  assert(expr.id()==ID_struct);
  assert(expr.operands().size()==2);
  return static_cast<string_exprt &>(expr);
}

inline const string_exprt &to_string_expr(const exprt &expr)
{
  assert(expr.id()==ID_struct);
  assert(expr.operands().size()==2);
  return static_cast<const string_exprt &>(expr);
}

#endif
