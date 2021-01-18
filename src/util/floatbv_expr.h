/*******************************************************************\

Module: API to expression classes for floating-point arithmetic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_FLOATBV_EXPR_H
#define CPROVER_UTIL_FLOATBV_EXPR_H

/// \file util/floatbv_expr.h
/// API to expression classes for floating-point arithmetic

#include "std_expr.h"

/// \brief Semantic type conversion from/to floating-point formats
class floatbv_typecast_exprt : public binary_exprt
{
public:
  floatbv_typecast_exprt(exprt op, exprt rounding, typet _type)
    : binary_exprt(
        std::move(op),
        ID_floatbv_typecast,
        std::move(rounding),
        std::move(_type))
  {
  }

  exprt &op()
  {
    return op0();
  }

  const exprt &op() const
  {
    return op0();
  }

  exprt &rounding_mode()
  {
    return op1();
  }

  const exprt &rounding_mode() const
  {
    return op1();
  }
};

template <>
inline bool can_cast_expr<floatbv_typecast_exprt>(const exprt &base)
{
  return base.id() == ID_floatbv_typecast;
}

inline void validate_expr(const floatbv_typecast_exprt &value)
{
  validate_operands(value, 2, "Float typecast must have two operands");
}

/// \brief Cast an exprt to a \ref floatbv_typecast_exprt
///
/// \a expr must be known to be \ref floatbv_typecast_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref floatbv_typecast_exprt
inline const floatbv_typecast_exprt &to_floatbv_typecast_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_floatbv_typecast);
  const floatbv_typecast_exprt &ret =
    static_cast<const floatbv_typecast_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_floatbv_typecast_expr(const exprt &)
inline floatbv_typecast_exprt &to_floatbv_typecast_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_floatbv_typecast);
  floatbv_typecast_exprt &ret = static_cast<floatbv_typecast_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Evaluates to true if the operand is NaN
class isnan_exprt : public unary_predicate_exprt
{
public:
  explicit isnan_exprt(exprt op)
    : unary_predicate_exprt(ID_isnan, std::move(op))
  {
  }
};

template <>
inline bool can_cast_expr<isnan_exprt>(const exprt &base)
{
  return base.id() == ID_isnan;
}

inline void validate_expr(const isnan_exprt &value)
{
  validate_operands(value, 1, "Is NaN must have one operand");
}

/// \brief Cast an exprt to a \ref isnan_exprt
///
/// \a expr must be known to be \ref isnan_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref isnan_exprt
inline const isnan_exprt &to_isnan_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_isnan);
  const isnan_exprt &ret = static_cast<const isnan_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_isnan_expr(const exprt &)
inline isnan_exprt &to_isnan_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_isnan);
  isnan_exprt &ret = static_cast<isnan_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Evaluates to true if the operand is infinite
class isinf_exprt : public unary_predicate_exprt
{
public:
  explicit isinf_exprt(exprt op)
    : unary_predicate_exprt(ID_isinf, std::move(op))
  {
  }
};

template <>
inline bool can_cast_expr<isinf_exprt>(const exprt &base)
{
  return base.id() == ID_isinf;
}

inline void validate_expr(const isinf_exprt &value)
{
  validate_operands(value, 1, "Is infinite must have one operand");
}

/// \brief Cast an exprt to a \ref isinf_exprt
///
/// \a expr must be known to be \ref isinf_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref isinf_exprt
inline const isinf_exprt &to_isinf_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_isinf);
  const isinf_exprt &ret = static_cast<const isinf_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_isinf_expr(const exprt &)
inline isinf_exprt &to_isinf_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_isinf);
  isinf_exprt &ret = static_cast<isinf_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Evaluates to true if the operand is finite
class isfinite_exprt : public unary_predicate_exprt
{
public:
  explicit isfinite_exprt(exprt op)
    : unary_predicate_exprt(ID_isfinite, std::move(op))
  {
  }
};

template <>
inline bool can_cast_expr<isfinite_exprt>(const exprt &base)
{
  return base.id() == ID_isfinite;
}

inline void validate_expr(const isfinite_exprt &value)
{
  validate_operands(value, 1, "Is finite must have one operand");
}

/// \brief Cast an exprt to a \ref isfinite_exprt
///
/// \a expr must be known to be \ref isfinite_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref isfinite_exprt
inline const isfinite_exprt &to_isfinite_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_isfinite);
  const isfinite_exprt &ret = static_cast<const isfinite_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_isfinite_expr(const exprt &)
inline isfinite_exprt &to_isfinite_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_isfinite);
  isfinite_exprt &ret = static_cast<isfinite_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Evaluates to true if the operand is a normal number
class isnormal_exprt : public unary_predicate_exprt
{
public:
  explicit isnormal_exprt(exprt op)
    : unary_predicate_exprt(ID_isnormal, std::move(op))
  {
  }
};

template <>
inline bool can_cast_expr<isnormal_exprt>(const exprt &base)
{
  return base.id() == ID_isnormal;
}

inline void validate_expr(const isnormal_exprt &value)
{
  validate_operands(value, 1, "Is normal must have one operand");
}

/// \brief Cast an exprt to a \ref isnormal_exprt
///
/// \a expr must be known to be \ref isnormal_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref isnormal_exprt
inline const isnormal_exprt &to_isnormal_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_isnormal);
  const isnormal_exprt &ret = static_cast<const isnormal_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_isnormal_expr(const exprt &)
inline isnormal_exprt &to_isnormal_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_isnormal);
  isnormal_exprt &ret = static_cast<isnormal_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief IEEE-floating-point equality
class ieee_float_equal_exprt : public binary_relation_exprt
{
public:
  ieee_float_equal_exprt(exprt _lhs, exprt _rhs)
    : binary_relation_exprt(
        std::move(_lhs),
        ID_ieee_float_equal,
        std::move(_rhs))
  {
  }
};

template <>
inline bool can_cast_expr<ieee_float_equal_exprt>(const exprt &base)
{
  return base.id() == ID_ieee_float_equal;
}

inline void validate_expr(const ieee_float_equal_exprt &value)
{
  validate_operands(value, 2, "IEEE equality must have two operands");
}

/// \brief Cast an exprt to an \ref ieee_float_equal_exprt
///
/// \a expr must be known to be \ref ieee_float_equal_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref ieee_float_equal_exprt
inline const ieee_float_equal_exprt &to_ieee_float_equal_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_ieee_float_equal);
  const ieee_float_equal_exprt &ret =
    static_cast<const ieee_float_equal_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_ieee_float_equal_expr(const exprt &)
inline ieee_float_equal_exprt &to_ieee_float_equal_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_ieee_float_equal);
  ieee_float_equal_exprt &ret = static_cast<ieee_float_equal_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief IEEE floating-point disequality
class ieee_float_notequal_exprt : public binary_relation_exprt
{
public:
  ieee_float_notequal_exprt(exprt _lhs, exprt _rhs)
    : binary_relation_exprt(
        std::move(_lhs),
        ID_ieee_float_notequal,
        std::move(_rhs))
  {
  }
};

template <>
inline bool can_cast_expr<ieee_float_notequal_exprt>(const exprt &base)
{
  return base.id() == ID_ieee_float_notequal;
}

inline void validate_expr(const ieee_float_notequal_exprt &value)
{
  validate_operands(value, 2, "IEEE inequality must have two operands");
}

/// \brief Cast an exprt to an \ref ieee_float_notequal_exprt
///
/// \a expr must be known to be \ref ieee_float_notequal_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref ieee_float_notequal_exprt
inline const ieee_float_notequal_exprt &
to_ieee_float_notequal_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_ieee_float_notequal);
  const ieee_float_notequal_exprt &ret =
    static_cast<const ieee_float_notequal_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_ieee_float_notequal_expr(const exprt &)
inline ieee_float_notequal_exprt &to_ieee_float_notequal_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_ieee_float_notequal);
  ieee_float_notequal_exprt &ret =
    static_cast<ieee_float_notequal_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief IEEE floating-point operations
/// These have two data operands (op0 and op1) and one rounding mode (op2).
/// The type of the result is that of the data operands.
class ieee_float_op_exprt : public ternary_exprt
{
public:
  ieee_float_op_exprt(
    const exprt &_lhs,
    const irep_idt &_id,
    exprt _rhs,
    exprt _rm)
    : ternary_exprt(_id, _lhs, std::move(_rhs), std::move(_rm), _lhs.type())
  {
  }

  exprt &lhs()
  {
    return op0();
  }

  const exprt &lhs() const
  {
    return op0();
  }

  exprt &rhs()
  {
    return op1();
  }

  const exprt &rhs() const
  {
    return op1();
  }

  exprt &rounding_mode()
  {
    return op2();
  }

  const exprt &rounding_mode() const
  {
    return op2();
  }
};

template <>
inline bool can_cast_expr<ieee_float_op_exprt>(const exprt &base)
{
  return base.id() == ID_floatbv_plus || base.id() == ID_floatbv_minus ||
         base.id() == ID_floatbv_div || base.id() == ID_floatbv_mult;
}

inline void validate_expr(const ieee_float_op_exprt &value)
{
  validate_operands(
    value, 3, "IEEE float operations must have three arguments");
}

/// \brief Cast an exprt to an \ref ieee_float_op_exprt
///
/// \a expr must be known to be \ref ieee_float_op_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref ieee_float_op_exprt
inline const ieee_float_op_exprt &to_ieee_float_op_expr(const exprt &expr)
{
  const ieee_float_op_exprt &ret =
    static_cast<const ieee_float_op_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_ieee_float_op_expr(const exprt &)
inline ieee_float_op_exprt &to_ieee_float_op_expr(exprt &expr)
{
  ieee_float_op_exprt &ret = static_cast<ieee_float_op_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

#endif // CPROVER_UTIL_FLOATBV_EXPR_H
