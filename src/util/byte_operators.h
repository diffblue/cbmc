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
class byte_extract_exprt : public binary_exprt
{
public:
  byte_extract_exprt(
    irep_idt _id,
    const exprt &_op,
    const exprt &_offset,
    std::size_t bits_per_byte,
    const typet &_type)
    : binary_exprt(_op, _id, _offset, _type)
  {
    INVARIANT(
      _id == ID_byte_extract_little_endian || _id == ID_byte_extract_big_endian,
      "byte_extract_exprt: Invalid ID");

    set_bits_per_byte(bits_per_byte);
  }

  exprt &op() { return op0(); }
  exprt &offset() { return op1(); }

  const exprt &op() const { return op0(); }
  const exprt &offset() const { return op1(); }

  std::size_t get_bits_per_byte() const
  {
    return get_size_t(ID_bits_per_byte);
  }

  void set_bits_per_byte(std::size_t bits_per_byte)
  {
    set_size_t(ID_bits_per_byte, bits_per_byte);
  }
};

template <>
inline bool can_cast_expr<byte_extract_exprt>(const exprt &base)
{
  return base.id() == ID_byte_extract_little_endian ||
         base.id() == ID_byte_extract_big_endian;
}

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

inline void validate_expr(const byte_extract_exprt &value)
{
  validate_operands(value, 2, "Byte extract must have two operands");
}

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
    const exprt &_value,
    std::size_t bits_per_byte)
    : ternary_exprt(_id, _op, _offset, _value, _op.type())
  {
    INVARIANT(
      _id == ID_byte_update_little_endian || _id == ID_byte_update_big_endian,
      "byte_update_exprt: Invalid ID");

    set_bits_per_byte(bits_per_byte);
  }

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

  std::size_t get_bits_per_byte() const
  {
    return get_size_t(ID_bits_per_byte);
  }

  void set_bits_per_byte(std::size_t bits_per_byte)
  {
    set_size_t(ID_bits_per_byte, bits_per_byte);
  }
};

template <>
inline bool can_cast_expr<byte_update_exprt>(const exprt &base)
{
  return base.id() == ID_byte_update_little_endian ||
         base.id() == ID_byte_update_big_endian;
}

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

/// Construct a byte_extract_exprt with endianness and byte width matching the
/// current configuration.
byte_extract_exprt
make_byte_extract(const exprt &_op, const exprt &_offset, const typet &_type);

/// Construct a byte_update_exprt with endianness and byte width matching the
/// current configuration.
byte_update_exprt
make_byte_update(const exprt &_op, const exprt &_offset, const exprt &_value);

/// Return true iff \p src or one of its operands contain a byte extract or byte
/// update expression.
bool has_byte_operator(const exprt &src);

/// Rewrite a byte extract expression to more fundamental operations.
/// \param src: Byte extract expression
/// \param ns: Namespace
/// \return Semantically equivalent expression such that the top-level
///   expression no longer is a \ref byte_extract_exprt or
///   \ref byte_update_exprt. Use \ref lower_byte_operators to also remove all
///   byte operators from any operands of \p src.
exprt lower_byte_extract(const byte_extract_exprt &src, const namespacet &ns);

/// Rewrite a byte update expression to more fundamental operations.
/// \param src: Byte update expression
/// \param ns: Namespace
/// \return Semantically equivalent expression such that the top-level
///   expression no longer is a \ref byte_extract_exprt or
///   \ref byte_update_exprt. Use \ref lower_byte_operators to also remove all
///   byte operators from any operands of \p src.
exprt lower_byte_update(const byte_update_exprt &src, const namespacet &ns);

/// Rewrite an expression possibly containing byte-extract or -update
/// expressions to more fundamental operations.
/// \param src: Input expression
/// \param ns: Namespace
/// \return Semantically equivalent expression that does not contain any \ref
///   byte_extract_exprt or \ref byte_update_exprt.
exprt lower_byte_operators(const exprt &src, const namespacet &ns);

#endif // CPROVER_UTIL_BYTE_OPERATORS_H
