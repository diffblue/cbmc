/******************************************************************\

Module: String expressions for the string solver

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// String expressions for the string solver

#ifndef CPROVER_UTIL_STRING_EXPR_H
#define CPROVER_UTIL_STRING_EXPR_H

#include "arith_tools.h"
#include "refined_string_type.h"
#include "std_expr.h"

// Given an representation of strings as exprt that implements `length` and
// `content` this provides additional useful methods.
template <typename child_t>
class string_exprt
{
private:
  exprt &length()
  {
    return static_cast<child_t *>(this)->length();
  }
  const exprt &length() const
  {
    return static_cast<const child_t *>(this)->length();
  }
  exprt &content()
  {
    return static_cast<child_t *>(this)->content();
  }
  const exprt &content() const
  {
    return static_cast<const child_t *>(this)->content();
  }

protected:
  string_exprt() = default;

public:
  exprt operator[](const exprt &i) const
  {
    return index_exprt(content(), i);
  }

  index_exprt operator[] (int i) const
  {
    return index_exprt(content(), from_integer(i, length().type()));
  }

  // Comparison on the length of the strings
  binary_relation_exprt axiom_for_length_ge(
    const string_exprt &rhs) const
  {
    return binary_relation_exprt(length(), ID_ge, rhs.length());
  }

  binary_relation_exprt axiom_for_length_ge(
    const exprt &rhs) const
  {
    PRECONDITION(rhs.type() == length().type());
    return binary_relation_exprt(length(), ID_ge, rhs);
  }

  binary_relation_exprt axiom_for_length_gt(
    const exprt &rhs) const
  {
    PRECONDITION(rhs.type() == length().type());
    return binary_relation_exprt(rhs, ID_lt, length());
  }

  binary_relation_exprt axiom_for_length_gt(
    const string_exprt &rhs) const
  {
    return binary_relation_exprt(rhs.length(), ID_lt, length());
  }

  binary_relation_exprt axiom_for_length_gt(mp_integer i) const
  {
    return axiom_for_length_gt(from_integer(i, length().type()));
  }

  binary_relation_exprt axiom_for_length_le(
    const string_exprt &rhs) const
  {
    return binary_relation_exprt(length(), ID_le, rhs.length());
  }

  binary_relation_exprt axiom_for_length_le(
    const exprt &rhs) const
  {
    PRECONDITION(rhs.type() == length().type());
    return binary_relation_exprt(length(), ID_le, rhs);
  }

  binary_relation_exprt axiom_for_length_le(mp_integer i) const
  {
    return axiom_for_length_le(from_integer(i, length().type()));
  }

  binary_relation_exprt axiom_for_length_lt(
    const string_exprt &rhs) const
  {
    return binary_relation_exprt(length(), ID_lt, rhs.length());
  }

  binary_relation_exprt axiom_for_length_lt(
    const exprt &rhs) const
  {
    PRECONDITION(rhs.type() == length().type());
    return binary_relation_exprt(length(), ID_lt, rhs);
  }

  equal_exprt axiom_for_has_same_length_as(
    const string_exprt &rhs) const
  {
    return equal_exprt(length(), rhs.length());
  }

  equal_exprt axiom_for_has_length(const exprt &rhs) const
  {
    PRECONDITION(rhs.type() == length().type());
    return equal_exprt(length(), rhs);
  }

  equal_exprt axiom_for_has_length(mp_integer i) const
  {
    return axiom_for_has_length(from_integer(i, length().type()));
  }
};

// Representation of strings as arrays
class array_string_exprt : public string_exprt<array_string_exprt>, public exprt
{
public:
  exprt &length()
  {
    return to_array_type(type()).size();
  }

  const exprt &length() const
  {
    return to_array_type(type()).size();
  }

  exprt &content()
  {
    return *this;
  }

  const exprt &content() const
  {
    return *this;
  }
};

inline array_string_exprt &to_array_string_expr(exprt &expr)
{
  PRECONDITION(expr.type().id() == ID_array);
  return static_cast<array_string_exprt &>(expr);
}

inline const array_string_exprt &to_array_string_expr(const exprt &expr)
{
  PRECONDITION(expr.type().id() == ID_array);
  return static_cast<const array_string_exprt &>(expr);
}

// Represent strings as a struct with a length field and a content field
class refined_string_exprt : public struct_exprt,
                             public string_exprt<refined_string_exprt>
{
public:
  refined_string_exprt() : struct_exprt()
  {
  }

  explicit refined_string_exprt(const typet &type) : struct_exprt(type)
  {
    operands().resize(2);
  }

  refined_string_exprt(
    const exprt &_length,
    const exprt &_content,
    const typet &type)
    : struct_exprt(type)
  {
    copy_to_operands(_length, _content);
  }

  refined_string_exprt(const exprt &_length, const exprt &_content)
    : refined_string_exprt(
        _length,
        _content,
        refined_string_typet(_length.type(), _content.type()))
  {
  }

  // Expression corresponding to the length of the string
  const exprt &length() const
  {
    return op0();
  }
  exprt &length()
  {
    return op0();
  }

  // Expression corresponding to the content (array of characters) of the string
  const exprt &content() const
  {
    return op1();
  }
  exprt &content()
  {
    return op1();
  }

  static exprt within_bounds(const exprt &idx, const exprt &bound);

  friend inline refined_string_exprt &to_string_expr(exprt &expr);
};

inline refined_string_exprt &to_string_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_struct);
  PRECONDITION(expr.operands().size()==2);
  return static_cast<refined_string_exprt &>(expr);
}

inline const refined_string_exprt &to_string_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_struct);
  PRECONDITION(expr.operands().size()==2);
  return static_cast<const refined_string_exprt &>(expr);
}

template <>
inline bool can_cast_expr<refined_string_exprt>(const exprt &base)
{
  return base.id() == ID_struct && base.operands().size() == 2;
}

inline void validate_expr(const refined_string_exprt &x)
{
  INVARIANT(x.id() == ID_struct, "refined string exprs are struct");
  validate_operands(x, 2, "refined string expr has length and content fields");
  INVARIANT(x.length().type().id() == ID_signedbv, "length is an unsigned int");
  INVARIANT(x.content().type().id() == ID_array, "content is an array");
}

#endif
