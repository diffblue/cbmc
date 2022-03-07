/*******************************************************************\

Module: API to expression classes for bitvectors

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_BITVECTOR_EXPR_H
#define CPROVER_UTIL_BITVECTOR_EXPR_H

/// \file util/bitvector_expr.h
/// API to expression classes for bitvectors

#include "std_expr.h"

/// \brief The byte swap expression
class bswap_exprt : public unary_exprt
{
public:
  bswap_exprt(exprt _op, std::size_t bits_per_byte, typet _type)
    : unary_exprt(ID_bswap, std::move(_op), std::move(_type))
  {
    set_bits_per_byte(bits_per_byte);
  }

  bswap_exprt(exprt _op, std::size_t bits_per_byte)
    : unary_exprt(ID_bswap, std::move(_op))
  {
    set_bits_per_byte(bits_per_byte);
  }

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
inline bool can_cast_expr<bswap_exprt>(const exprt &base)
{
  return base.id() == ID_bswap;
}

inline void validate_expr(const bswap_exprt &value)
{
  validate_operands(value, 1, "bswap must have one operand");
  DATA_INVARIANT(
    value.op().type() == value.type(), "bswap type must match operand type");
}

/// \brief Cast an exprt to a \ref bswap_exprt
///
/// \a expr must be known to be \ref bswap_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref bswap_exprt
inline const bswap_exprt &to_bswap_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_bswap);
  const bswap_exprt &ret = static_cast<const bswap_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_bswap_expr(const exprt &)
inline bswap_exprt &to_bswap_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_bswap);
  bswap_exprt &ret = static_cast<bswap_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Bit-wise negation of bit-vectors
class bitnot_exprt : public unary_exprt
{
public:
  explicit bitnot_exprt(exprt op) : unary_exprt(ID_bitnot, std::move(op))
  {
  }
};

template <>
inline bool can_cast_expr<bitnot_exprt>(const exprt &base)
{
  return base.id() == ID_bitnot;
}

inline void validate_expr(const bitnot_exprt &value)
{
  validate_operands(value, 1, "Bit-wise not must have one operand");
}

/// \brief Cast an exprt to a \ref bitnot_exprt
///
/// \a expr must be known to be \ref bitnot_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref bitnot_exprt
inline const bitnot_exprt &to_bitnot_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_bitnot);
  const bitnot_exprt &ret = static_cast<const bitnot_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_bitnot_expr(const exprt &)
inline bitnot_exprt &to_bitnot_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_bitnot);
  bitnot_exprt &ret = static_cast<bitnot_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Bit-wise OR
class bitor_exprt : public multi_ary_exprt
{
public:
  bitor_exprt(const exprt &_op0, exprt _op1)
    : multi_ary_exprt(_op0, ID_bitor, std::move(_op1), _op0.type())
  {
  }
};

template <>
inline bool can_cast_expr<bitor_exprt>(const exprt &base)
{
  return base.id() == ID_bitor;
}

/// \brief Cast an exprt to a \ref bitor_exprt
///
/// \a expr must be known to be \ref bitor_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref bitor_exprt
inline const bitor_exprt &to_bitor_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_bitor);
  return static_cast<const bitor_exprt &>(expr);
}

/// \copydoc to_bitor_expr(const exprt &)
inline bitor_exprt &to_bitor_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_bitor);
  return static_cast<bitor_exprt &>(expr);
}

/// \brief Bit-wise XOR
class bitxor_exprt : public multi_ary_exprt
{
public:
  bitxor_exprt(exprt _op0, exprt _op1)
    : multi_ary_exprt(std::move(_op0), ID_bitxor, std::move(_op1))
  {
  }
};

template <>
inline bool can_cast_expr<bitxor_exprt>(const exprt &base)
{
  return base.id() == ID_bitxor;
}

/// \brief Cast an exprt to a \ref bitxor_exprt
///
/// \a expr must be known to be \ref bitxor_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref bitxor_exprt
inline const bitxor_exprt &to_bitxor_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_bitxor);
  return static_cast<const bitxor_exprt &>(expr);
}

/// \copydoc to_bitxor_expr(const exprt &)
inline bitxor_exprt &to_bitxor_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_bitxor);
  return static_cast<bitxor_exprt &>(expr);
}

/// \brief Bit-wise AND
class bitand_exprt : public multi_ary_exprt
{
public:
  bitand_exprt(const exprt &_op0, exprt _op1)
    : multi_ary_exprt(_op0, ID_bitand, std::move(_op1), _op0.type())
  {
  }
};

template <>
inline bool can_cast_expr<bitand_exprt>(const exprt &base)
{
  return base.id() == ID_bitand;
}

/// \brief Cast an exprt to a \ref bitand_exprt
///
/// \a expr must be known to be \ref bitand_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref bitand_exprt
inline const bitand_exprt &to_bitand_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_bitand);
  return static_cast<const bitand_exprt &>(expr);
}

/// \copydoc to_bitand_expr(const exprt &)
inline bitand_exprt &to_bitand_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_bitand);
  return static_cast<bitand_exprt &>(expr);
}

/// \brief A base class for shift and rotate operators
class shift_exprt : public binary_exprt
{
public:
  shift_exprt(exprt _src, const irep_idt &_id, exprt _distance)
    : binary_exprt(std::move(_src), _id, std::move(_distance))
  {
  }

  shift_exprt(exprt _src, const irep_idt &_id, const std::size_t _distance);

  exprt &op()
  {
    return op0();
  }

  const exprt &op() const
  {
    return op0();
  }

  exprt &distance()
  {
    return op1();
  }

  const exprt &distance() const
  {
    return op1();
  }
};

template <>
inline bool can_cast_expr<shift_exprt>(const exprt &base)
{
  return base.id() == ID_shl || base.id() == ID_ashr || base.id() == ID_lshr ||
         base.id() == ID_ror || base.id() == ID_rol;
}

inline void validate_expr(const shift_exprt &value)
{
  validate_operands(value, 2, "Shifts must have two operands");
}

/// \brief Cast an exprt to a \ref shift_exprt
///
/// \a expr must be known to be \ref shift_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref shift_exprt
inline const shift_exprt &to_shift_expr(const exprt &expr)
{
  const shift_exprt &ret = static_cast<const shift_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_shift_expr(const exprt &)
inline shift_exprt &to_shift_expr(exprt &expr)
{
  shift_exprt &ret = static_cast<shift_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Left shift
class shl_exprt : public shift_exprt
{
public:
  shl_exprt(exprt _src, exprt _distance)
    : shift_exprt(std::move(_src), ID_shl, std::move(_distance))
  {
  }

  shl_exprt(exprt _src, const std::size_t _distance)
    : shift_exprt(std::move(_src), ID_shl, _distance)
  {
  }
};

template <>
inline bool can_cast_expr<shl_exprt>(const exprt &base)
{
  return base.id() == ID_shl;
}

/// \brief Cast an exprt to a \ref shl_exprt
///
/// \a expr must be known to be \ref shl_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref shl_exprt
inline const shl_exprt &to_shl_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_shl);
  const shl_exprt &ret = static_cast<const shl_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_shl_expr(const exprt &)
inline shl_exprt &to_shl_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_shl);
  shl_exprt &ret = static_cast<shl_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Arithmetic right shift
class ashr_exprt : public shift_exprt
{
public:
  ashr_exprt(exprt _src, exprt _distance)
    : shift_exprt(std::move(_src), ID_ashr, std::move(_distance))
  {
  }

  ashr_exprt(exprt _src, const std::size_t _distance)
    : shift_exprt(std::move(_src), ID_ashr, _distance)
  {
  }
};

template <>
inline bool can_cast_expr<ashr_exprt>(const exprt &base)
{
  return base.id() == ID_ashr;
}

/// \brief Logical right shift
class lshr_exprt : public shift_exprt
{
public:
  lshr_exprt(exprt _src, exprt _distance)
    : shift_exprt(std::move(_src), ID_lshr, std::move(_distance))
  {
  }

  lshr_exprt(exprt _src, const std::size_t _distance)
    : shift_exprt(std::move(_src), ID_lshr, std::move(_distance))
  {
  }
};

template <>
inline bool can_cast_expr<lshr_exprt>(const exprt &base)
{
  return base.id() == ID_lshr;
}

/// \brief Extracts a single bit of a bit-vector operand
class extractbit_exprt : public binary_predicate_exprt
{
public:
  /// Extract the \p _index-th least significant bit from \p _src.
  extractbit_exprt(exprt _src, exprt _index)
    : binary_predicate_exprt(std::move(_src), ID_extractbit, std::move(_index))
  {
  }

  extractbit_exprt(exprt _src, const std::size_t _index);

  exprt &src()
  {
    return op0();
  }

  exprt &index()
  {
    return op1();
  }

  const exprt &src() const
  {
    return op0();
  }

  const exprt &index() const
  {
    return op1();
  }
};

template <>
inline bool can_cast_expr<extractbit_exprt>(const exprt &base)
{
  return base.id() == ID_extractbit;
}

inline void validate_expr(const extractbit_exprt &value)
{
  validate_operands(value, 2, "Extract bit must have two operands");
}

/// \brief Cast an exprt to an \ref extractbit_exprt
///
/// \a expr must be known to be \ref extractbit_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref extractbit_exprt
inline const extractbit_exprt &to_extractbit_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_extractbit);
  const extractbit_exprt &ret = static_cast<const extractbit_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_extractbit_expr(const exprt &)
inline extractbit_exprt &to_extractbit_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_extractbit);
  extractbit_exprt &ret = static_cast<extractbit_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Extracts a sub-range of a bit-vector operand
class extractbits_exprt : public expr_protectedt
{
public:
  /// Extract the bits [\p _lower .. \p _upper] from \p _src to produce a result
  /// of type \p _type. Note that this specifies a closed interval, i.e., both
  /// bits \p _lower and \p _upper are included. Indices count from the
  /// least-significant bit, and are not affected by endianness.
  /// The ordering upper-lower matches what SMT-LIB uses.
  extractbits_exprt(exprt _src, exprt _upper, exprt _lower, typet _type)
    : expr_protectedt(
        ID_extractbits,
        std::move(_type),
        {std::move(_src), std::move(_upper), std::move(_lower)})
  {
  }

  extractbits_exprt(
    exprt _src,
    const std::size_t _upper,
    const std::size_t _lower,
    typet _type);

  exprt &src()
  {
    return op0();
  }

  exprt &upper()
  {
    return op1();
  }

  exprt &lower()
  {
    return op2();
  }

  const exprt &src() const
  {
    return op0();
  }

  const exprt &upper() const
  {
    return op1();
  }

  const exprt &lower() const
  {
    return op2();
  }
};

template <>
inline bool can_cast_expr<extractbits_exprt>(const exprt &base)
{
  return base.id() == ID_extractbits;
}

inline void validate_expr(const extractbits_exprt &value)
{
  validate_operands(value, 3, "Extract bits must have three operands");
}

/// \brief Cast an exprt to an \ref extractbits_exprt
///
/// \a expr must be known to be \ref extractbits_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref extractbits_exprt
inline const extractbits_exprt &to_extractbits_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_extractbits);
  const extractbits_exprt &ret = static_cast<const extractbits_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_extractbits_expr(const exprt &)
inline extractbits_exprt &to_extractbits_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_extractbits);
  extractbits_exprt &ret = static_cast<extractbits_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Bit-vector replication
class replication_exprt : public binary_exprt
{
public:
  replication_exprt(constant_exprt _times, exprt _src, typet _type)
    : binary_exprt(
        std::move(_times),
        ID_replication,
        std::move(_src),
        std::move(_type))
  {
  }

  constant_exprt &times()
  {
    return static_cast<constant_exprt &>(op0());
  }

  const constant_exprt &times() const
  {
    return static_cast<const constant_exprt &>(op0());
  }

  exprt &op()
  {
    return op1();
  }

  const exprt &op() const
  {
    return op1();
  }
};

template <>
inline bool can_cast_expr<replication_exprt>(const exprt &base)
{
  return base.id() == ID_replication;
}

inline void validate_expr(const replication_exprt &value)
{
  validate_operands(value, 2, "Bit-wise replication must have two operands");
}

/// \brief Cast an exprt to a \ref replication_exprt
///
/// \a expr must be known to be \ref replication_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref replication_exprt
inline const replication_exprt &to_replication_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_replication);
  const replication_exprt &ret = static_cast<const replication_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_replication_expr(const exprt &)
inline replication_exprt &to_replication_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_replication);
  replication_exprt &ret = static_cast<replication_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Concatenation of bit-vector operands
///
/// This expression takes any number of operands
/// The ordering of the operands is the same as in the SMT-LIB 2 standard,
/// i.e., most-significant operands come first.
class concatenation_exprt : public multi_ary_exprt
{
public:
  concatenation_exprt(operandst _operands, typet _type)
    : multi_ary_exprt(ID_concatenation, std::move(_operands), std::move(_type))
  {
  }

  concatenation_exprt(exprt _op0, exprt _op1, typet _type)
    : multi_ary_exprt(
        ID_concatenation,
        {std::move(_op0), std::move(_op1)},
        std::move(_type))
  {
  }
};

template <>
inline bool can_cast_expr<concatenation_exprt>(const exprt &base)
{
  return base.id() == ID_concatenation;
}

/// \brief Cast an exprt to a \ref concatenation_exprt
///
/// \a expr must be known to be \ref concatenation_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref concatenation_exprt
inline const concatenation_exprt &to_concatenation_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_concatenation);
  return static_cast<const concatenation_exprt &>(expr);
}

/// \copydoc to_concatenation_expr(const exprt &)
inline concatenation_exprt &to_concatenation_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_concatenation);
  return static_cast<concatenation_exprt &>(expr);
}

/// \brief The popcount (counting the number of bits set to 1) expression
class popcount_exprt : public unary_exprt
{
public:
  popcount_exprt(exprt _op, typet _type)
    : unary_exprt(ID_popcount, std::move(_op), std::move(_type))
  {
  }

  explicit popcount_exprt(const exprt &_op)
    : unary_exprt(ID_popcount, _op, _op.type())
  {
  }

  /// Lower a popcount_exprt to arithmetic and logic expressions.
  /// \return Semantically equivalent expression
  exprt lower() const;
};

template <>
inline bool can_cast_expr<popcount_exprt>(const exprt &base)
{
  return base.id() == ID_popcount;
}

inline void validate_expr(const popcount_exprt &value)
{
  validate_operands(value, 1, "popcount must have one operand");
}

/// \brief Cast an exprt to a \ref popcount_exprt
///
/// \a expr must be known to be \ref popcount_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref popcount_exprt
inline const popcount_exprt &to_popcount_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_popcount);
  const popcount_exprt &ret = static_cast<const popcount_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_popcount_expr(const exprt &)
inline popcount_exprt &to_popcount_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_popcount);
  popcount_exprt &ret = static_cast<popcount_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief A Boolean expression returning true, iff operation \c kind would
/// result in an overflow when applied to operands \c lhs and \c rhs.
class binary_overflow_exprt : public binary_predicate_exprt
{
public:
  binary_overflow_exprt(exprt _lhs, const irep_idt &kind, exprt _rhs)
    : binary_predicate_exprt(std::move(_lhs), make_id(kind), std::move(_rhs))
  {
  }

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    binary_exprt::check(expr, vm);

    if(expr.id() != ID_overflow_shl)
    {
      const binary_exprt &binary_expr = to_binary_expr(expr);
      DATA_CHECK(
        vm,
        binary_expr.lhs().type() == binary_expr.rhs().type(),
        "operand types must match");
    }
  }

  static void validate(
    const exprt &expr,
    const namespacet &,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    check(expr, vm);
  }

  /// Returns true iff \p id is a valid identifier of a `binary_overflow_exprt`.
  static bool valid_id(const irep_idt &id)
  {
    return id == ID_overflow_plus || id == ID_overflow_mult ||
           id == ID_overflow_minus || id == ID_overflow_shl;
  }

private:
  static irep_idt make_id(const irep_idt &kind)
  {
    if(valid_id(kind))
      return kind;
    else
      return "overflow-" + id2string(kind);
  }
};

template <>
inline bool can_cast_expr<binary_overflow_exprt>(const exprt &base)
{
  return binary_overflow_exprt::valid_id(base.id());
}

inline void validate_expr(const binary_overflow_exprt &value)
{
  validate_operands(
    value, 2, "binary overflow expression must have two operands");
}

/// \brief Cast an exprt to a \ref binary_overflow_exprt
///
/// \a expr must be known to be \ref binary_overflow_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref binary_overflow_exprt
inline const binary_overflow_exprt &to_binary_overflow_expr(const exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_overflow_plus || expr.id() == ID_overflow_mult ||
    expr.id() == ID_overflow_minus || expr.id() == ID_overflow_shl);
  const binary_overflow_exprt &ret =
    static_cast<const binary_overflow_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_binary_overflow_expr(const exprt &)
inline binary_overflow_exprt &to_binary_overflow_expr(exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_overflow_plus || expr.id() == ID_overflow_mult ||
    expr.id() == ID_overflow_minus || expr.id() == ID_overflow_shl);
  binary_overflow_exprt &ret = static_cast<binary_overflow_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class plus_overflow_exprt : public binary_overflow_exprt
{
public:
  plus_overflow_exprt(exprt _lhs, exprt _rhs)
    : binary_overflow_exprt(std::move(_lhs), ID_overflow_plus, std::move(_rhs))
  {
  }
};

template <>
inline bool can_cast_expr<plus_overflow_exprt>(const exprt &base)
{
  return base.id() == ID_overflow_plus;
}

class minus_overflow_exprt : public binary_overflow_exprt
{
public:
  minus_overflow_exprt(exprt _lhs, exprt _rhs)
    : binary_overflow_exprt(std::move(_lhs), ID_overflow_minus, std::move(_rhs))
  {
  }
};

template <>
inline bool can_cast_expr<minus_overflow_exprt>(const exprt &base)
{
  return base.id() == ID_overflow_minus;
}

class mult_overflow_exprt : public binary_overflow_exprt
{
public:
  mult_overflow_exprt(exprt _lhs, exprt _rhs)
    : binary_overflow_exprt(std::move(_lhs), ID_overflow_mult, std::move(_rhs))
  {
  }
};

template <>
inline bool can_cast_expr<mult_overflow_exprt>(const exprt &base)
{
  return base.id() == ID_overflow_mult;
}

class shl_overflow_exprt : public binary_overflow_exprt
{
public:
  shl_overflow_exprt(exprt _lhs, exprt _rhs)
    : binary_overflow_exprt(std::move(_lhs), ID_overflow_shl, std::move(_rhs))
  {
  }
};

template <>
inline bool can_cast_expr<shl_overflow_exprt>(const exprt &base)
{
  return base.id() == ID_overflow_shl;
}

/// \brief A Boolean expression returning true, iff operation \c kind would
/// result in an overflow when applied to the (single) operand.
class unary_overflow_exprt : public unary_predicate_exprt
{
public:
  unary_overflow_exprt(const irep_idt &kind, exprt _op)
    : unary_predicate_exprt("overflow-" + id2string(kind), std::move(_op))
  {
  }

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    unary_exprt::check(expr, vm);
  }

  static void validate(
    const exprt &expr,
    const namespacet &,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    check(expr, vm);
  }
};

template <>
inline bool can_cast_expr<unary_overflow_exprt>(const exprt &base)
{
  return base.id() == ID_overflow_unary_minus;
}

inline void validate_expr(const unary_overflow_exprt &value)
{
  validate_operands(
    value, 1, "unary overflow expression must have one operand");
}

/// \brief Cast an exprt to a \ref unary_overflow_exprt
///
/// \a expr must be known to be \ref unary_overflow_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref unary_overflow_exprt
inline const unary_overflow_exprt &to_unary_overflow_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_overflow_unary_minus);
  const unary_overflow_exprt &ret =
    static_cast<const unary_overflow_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_unary_overflow_expr(const exprt &)
inline unary_overflow_exprt &to_unary_overflow_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_overflow_unary_minus);
  unary_overflow_exprt &ret = static_cast<unary_overflow_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief The count leading zeros (counting the number of zero bits starting
/// from the most-significant bit) expression. When \c zero_permitted is set to
/// false, goto_checkt must generate an assertion that the operand does not
/// evaluate to zero. The result is always defined, even for zero (where the
/// result is the bit width).
class count_leading_zeros_exprt : public unary_exprt
{
public:
  count_leading_zeros_exprt(exprt _op, bool _zero_permitted, typet _type)
    : unary_exprt(ID_count_leading_zeros, std::move(_op), std::move(_type))
  {
    zero_permitted(_zero_permitted);
  }

  explicit count_leading_zeros_exprt(const exprt &_op)
    : count_leading_zeros_exprt(_op, true, _op.type())
  {
  }

  bool zero_permitted() const
  {
    return !get_bool(ID_C_bounds_check);
  }

  void zero_permitted(bool value)
  {
    set(ID_C_bounds_check, !value);
  }

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm,
      expr.operands().size() == 1,
      "unary expression must have a single operand");
    DATA_CHECK(
      vm,
      can_cast_type<bitvector_typet>(to_unary_expr(expr).op().type()),
      "operand must be of bitvector type");
  }

  static void validate(
    const exprt &expr,
    const namespacet &,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    check(expr, vm);
  }

  /// Lower a count_leading_zeros_exprt to arithmetic and logic expressions.
  /// \return Semantically equivalent expression
  exprt lower() const;
};

template <>
inline bool can_cast_expr<count_leading_zeros_exprt>(const exprt &base)
{
  return base.id() == ID_count_leading_zeros;
}

inline void validate_expr(const count_leading_zeros_exprt &value)
{
  validate_operands(value, 1, "count_leading_zeros must have one operand");
}

/// \brief Cast an exprt to a \ref count_leading_zeros_exprt
///
/// \a expr must be known to be \ref count_leading_zeros_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref count_leading_zeros_exprt
inline const count_leading_zeros_exprt &
to_count_leading_zeros_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_count_leading_zeros);
  const count_leading_zeros_exprt &ret =
    static_cast<const count_leading_zeros_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_count_leading_zeros_expr(const exprt &)
inline count_leading_zeros_exprt &to_count_leading_zeros_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_count_leading_zeros);
  count_leading_zeros_exprt &ret =
    static_cast<count_leading_zeros_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief The count trailing zeros (counting the number of zero bits starting
/// from the least-significant bit) expression. When \c zero_permitted is set to
/// false, goto_checkt must generate an assertion that the operand does not
/// evaluate to zero. The result is always defined, even for zero (where the
/// result is the bit width).
class count_trailing_zeros_exprt : public unary_exprt
{
public:
  count_trailing_zeros_exprt(exprt _op, bool _zero_permitted, typet _type)
    : unary_exprt(ID_count_trailing_zeros, std::move(_op), std::move(_type))
  {
    zero_permitted(_zero_permitted);
  }

  explicit count_trailing_zeros_exprt(const exprt &_op)
    : count_trailing_zeros_exprt(_op, true, _op.type())
  {
  }

  bool zero_permitted() const
  {
    return !get_bool(ID_C_bounds_check);
  }

  void zero_permitted(bool value)
  {
    set(ID_C_bounds_check, !value);
  }

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm,
      expr.operands().size() == 1,
      "unary expression must have a single operand");
    DATA_CHECK(
      vm,
      can_cast_type<bitvector_typet>(to_unary_expr(expr).op().type()),
      "operand must be of bitvector type");
  }

  static void validate(
    const exprt &expr,
    const namespacet &,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    check(expr, vm);
  }

  /// Lower a count_trailing_zeros_exprt to arithmetic and logic expressions.
  /// \return Semantically equivalent expression
  exprt lower() const;
};

template <>
inline bool can_cast_expr<count_trailing_zeros_exprt>(const exprt &base)
{
  return base.id() == ID_count_trailing_zeros;
}

inline void validate_expr(const count_trailing_zeros_exprt &value)
{
  validate_operands(value, 1, "count_trailing_zeros must have one operand");
}

/// \brief Cast an exprt to a \ref count_trailing_zeros_exprt
///
/// \a expr must be known to be \ref count_trailing_zeros_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref count_trailing_zeros_exprt
inline const count_trailing_zeros_exprt &
to_count_trailing_zeros_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_count_trailing_zeros);
  const count_trailing_zeros_exprt &ret =
    static_cast<const count_trailing_zeros_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_count_trailing_zeros_expr(const exprt &)
inline count_trailing_zeros_exprt &to_count_trailing_zeros_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_count_trailing_zeros);
  count_trailing_zeros_exprt &ret =
    static_cast<count_trailing_zeros_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Reverse the order of bits in a bit-vector.
class bitreverse_exprt : public unary_exprt
{
public:
  explicit bitreverse_exprt(exprt op)
    : unary_exprt(ID_bitreverse, std::move(op))
  {
  }

  /// Lower a bitreverse_exprt to arithmetic and logic expressions.
  /// \return Semantically equivalent expression
  exprt lower() const;
};

template <>
inline bool can_cast_expr<bitreverse_exprt>(const exprt &base)
{
  return base.id() == ID_bitreverse;
}

inline void validate_expr(const bitreverse_exprt &value)
{
  validate_operands(value, 1, "Bit-wise reverse must have one operand");
}

/// \brief Cast an exprt to a \ref bitreverse_exprt
///
/// \a expr must be known to be \ref bitreverse_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref bitreverse_exprt
inline const bitreverse_exprt &to_bitreverse_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_bitreverse);
  const bitreverse_exprt &ret = static_cast<const bitreverse_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_bitreverse_expr(const exprt &)
inline bitreverse_exprt &to_bitreverse_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_bitreverse);
  bitreverse_exprt &ret = static_cast<bitreverse_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief The saturating plus expression
class saturating_plus_exprt : public binary_exprt
{
public:
  saturating_plus_exprt(exprt _lhs, exprt _rhs)
    : binary_exprt(std::move(_lhs), ID_saturating_plus, std::move(_rhs))
  {
  }

  saturating_plus_exprt(exprt _lhs, exprt _rhs, typet _type)
    : binary_exprt(
        std::move(_lhs),
        ID_saturating_plus,
        std::move(_rhs),
        std::move(_type))
  {
  }
};

template <>
inline bool can_cast_expr<saturating_plus_exprt>(const exprt &base)
{
  return base.id() == ID_saturating_plus;
}

inline void validate_expr(const saturating_plus_exprt &value)
{
  validate_operands(value, 2, "saturating plus must have two operands");
}

/// \brief Cast an exprt to a \ref saturating_plus_exprt
///
/// \a expr must be known to be \ref saturating_plus_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref saturating_plus_exprt
inline const saturating_plus_exprt &to_saturating_plus_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_saturating_plus);
  const saturating_plus_exprt &ret =
    static_cast<const saturating_plus_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_saturating_plus_expr(const exprt &)
inline saturating_plus_exprt &to_saturating_plus_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_saturating_plus);
  saturating_plus_exprt &ret = static_cast<saturating_plus_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Saturating subtraction expression.
class saturating_minus_exprt : public binary_exprt
{
public:
  saturating_minus_exprt(exprt _lhs, exprt _rhs)
    : binary_exprt(std::move(_lhs), ID_saturating_minus, std::move(_rhs))
  {
  }
};

template <>
inline bool can_cast_expr<saturating_minus_exprt>(const exprt &base)
{
  return base.id() == ID_saturating_minus;
}

inline void validate_expr(const saturating_minus_exprt &value)
{
  validate_operands(value, 2, "saturating minus must have two operands");
}

/// \brief Cast an exprt to a \ref saturating_minus_exprt
///
/// \a expr must be known to be \ref saturating_minus_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref saturating_minus_exprt
inline const saturating_minus_exprt &to_saturating_minus_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_saturating_minus);
  const saturating_minus_exprt &ret =
    static_cast<const saturating_minus_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_saturating_minus_expr(const exprt &)
inline saturating_minus_exprt &to_saturating_minus_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_saturating_minus);
  saturating_minus_exprt &ret = static_cast<saturating_minus_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

#endif // CPROVER_UTIL_BITVECTOR_EXPR_H
