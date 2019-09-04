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

inline binary_relation_exprt greater_or_equal_to(exprt lhs, exprt rhs)
{
  PRECONDITION(rhs.type() == lhs.type());
  return binary_relation_exprt(std::move(lhs), ID_ge, std::move(rhs));
}

inline binary_relation_exprt greater_than(exprt lhs, exprt rhs)
{
  PRECONDITION(rhs.type() == lhs.type());
  return binary_relation_exprt(std::move(rhs), ID_lt, std::move(lhs));
}

inline binary_relation_exprt greater_than(const exprt &lhs, mp_integer i)
{
  return binary_relation_exprt(from_integer(i, lhs.type()), ID_lt, lhs);
}

inline binary_relation_exprt less_than_or_equal_to(exprt lhs, exprt rhs)
{
  PRECONDITION(rhs.type() == lhs.type());
  return binary_relation_exprt(std::move(lhs), ID_le, std::move(rhs));
}

inline binary_relation_exprt
less_than_or_equal_to(const exprt &lhs, mp_integer i)
{
  return binary_relation_exprt(lhs, ID_le, from_integer(i, lhs.type()));
}

inline binary_relation_exprt less_than(exprt lhs, exprt rhs)
{
  PRECONDITION(rhs.type() == lhs.type());
  return binary_relation_exprt(std::move(lhs), ID_lt, std::move(rhs));
}

inline equal_exprt equal_to(exprt lhs, exprt rhs)
{
  PRECONDITION(rhs.type() == lhs.type());
  return equal_exprt(std::move(lhs), std::move(rhs));
}

inline equal_exprt equal_to(const exprt &lhs, mp_integer i)
{
  return equal_exprt(lhs, from_integer(i, lhs.type()));
}

// Representation of strings as arrays
class array_string_exprt : public exprt
{
public:
  const typet &length_type() const
  {
    return to_array_type(type()).size().type();
  }

  exprt &content()
  {
    return *this;
  }

  const exprt &content() const
  {
    return *this;
  }

  exprt operator[](const exprt &i) const
  {
    return index_exprt(content(), i);
  }

  index_exprt operator[](int i) const
  {
    return index_exprt(content(), from_integer(i, length_type()));
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
class refined_string_exprt : public struct_exprt
{
public:
  refined_string_exprt(
    const exprt &_length,
    const exprt &_content,
    const typet &type)
    : struct_exprt({_length, _content}, type)
  {
  }

  refined_string_exprt(const exprt &_length, const exprt &_content)
    : refined_string_exprt(
        _length,
        _content,
        refined_string_typet(_length.type(), to_pointer_type(_content.type())))
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
  return base.id() == ID_struct && base.operands().size() == 2 &&
    is_refined_string_type(base.type());
}

inline void validate_expr(const refined_string_exprt &x)
{
  INVARIANT(x.id() == ID_struct, "refined string exprs are struct");
  validate_operands(x, 2, "refined string expr has length and content fields");
  INVARIANT(
    x.length().type().id() == ID_signedbv, "length should be a signed int");
  INVARIANT(x.content().type().id() == ID_array, "content should be an array");
}

#endif
