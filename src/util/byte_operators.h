/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_BYTE_OPERATORS_H
#define CPROVER_UTIL_BYTE_OPERATORS_H

/*! \file util/byte_operators.h
 * \brief Expression classes for byte-level operators
 *
 * \author Daniel Kroening <kroening@kroening.com>
 * \date   Sun Jul 31 21:54:44 BST 2011
*/

#include "invariant.h"
#include "std_expr.h"

/// Expression of type \c type extracted from some object \c op starting at
/// position \c offset (given in number of bytes).
/// The object can either be interpreted in big endian or little endian, which
/// is reflected by the \c id of the expression which is either
/// \c ID_byte_extract_big_endian or \c ID_byte_extract_little_endian
class byte_extract_exprt:public binary_exprt
{
public:
  DEPRECATED(
    SINCE(2019, 1, 12, "use byte_extract_exprt(id, op, offset, type) instead"))
  explicit byte_extract_exprt(irep_idt _id):binary_exprt(_id)
  {
  }

  DEPRECATED(
    SINCE(2019, 1, 12, "use byte_extract_exprt(id, op, offset, type) instead"))
  explicit byte_extract_exprt(irep_idt _id, const typet &_type):
    binary_exprt(_id, _type)
  {
  }

  byte_extract_exprt(
    irep_idt _id,
    const exprt &_op,
    const exprt &_offset,
    const typet &_type)
    : binary_exprt(_op, _id, _offset, _type)
  {
  }

  exprt &op() { return op0(); }
  exprt &offset() { return op1(); }

  const exprt &op() const { return op0(); }
  const exprt &offset() const { return op1(); }
};

inline const byte_extract_exprt &to_byte_extract_expr(const exprt &expr)
{
  PRECONDITION(expr.operands().size() == 2);
  return static_cast<const byte_extract_exprt &>(expr);
}

inline byte_extract_exprt &to_byte_extract_expr(exprt &expr)
{
  PRECONDITION(expr.operands().size() == 2);
  return static_cast<byte_extract_exprt &>(expr);
}

irep_idt byte_extract_id();
irep_idt byte_update_id();

/// Expression corresponding to \c op() where the bytes starting at
/// position \c offset (given in number of bytes) have been updated with
/// \c value.
class byte_update_exprt : public ternary_exprt
{
public:
  byte_update_exprt(
    irep_idt _id,
    const exprt &_op,
    const exprt &_offset,
    const exprt &_value)
    : ternary_exprt(_id, _op, _offset, _value, _op.type())
  {
  }

  exprt &op() { return op0(); }
  exprt &offset() { return op1(); }
  exprt &value() { return op2(); }
  void set_op(exprt e)
  {
    op0() = std::move(e);
  }
  void set_offset(exprt e)
  {
    op1() = std::move(e);
  }
  void set_value(exprt e)
  {
    op2() = std::move(e);
  }

  const exprt &op() const { return op0(); }
  const exprt &offset() const { return op1(); }
  const exprt &value() const { return op2(); }
};

inline const byte_update_exprt &to_byte_update_expr(const exprt &expr)
{
  PRECONDITION(expr.operands().size() == 3);
  return static_cast<const byte_update_exprt &>(expr);
}

inline byte_update_exprt &to_byte_update_expr(exprt &expr)
{
  PRECONDITION(expr.operands().size() == 3);
  return static_cast<byte_update_exprt &>(expr);
}

#endif // CPROVER_UTIL_BYTE_OPERATORS_H
