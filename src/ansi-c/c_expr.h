/*******************************************************************\

Module: API to expression classes that are internal to the C frontend

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_C_EXPR_H
#define CPROVER_ANSI_C_C_EXPR_H

/// \file ansi-c/c_expr.h
/// API to expression classes that are internal to the C frontend

#include <util/std_code.h>

/// \brief Shuffle elements of one or two vectors, modelled after Clang's
/// __builtin_shufflevector.
class shuffle_vector_exprt : public multi_ary_exprt
{
public:
  shuffle_vector_exprt(
    exprt vector1,
    optionalt<exprt> vector2,
    exprt::operandst indices);

  const vector_typet &type() const
  {
    return static_cast<const vector_typet &>(multi_ary_exprt::type());
  }

  vector_typet &type()
  {
    return static_cast<vector_typet &>(multi_ary_exprt::type());
  }

  const exprt &vector1() const
  {
    return op0();
  }

  exprt &vector1()
  {
    return op0();
  }

  const exprt &vector2() const
  {
    return op1();
  }

  exprt &vector2()
  {
    return op1();
  }

  bool has_two_input_vectors() const
  {
    return vector2().is_not_nil();
  }

  const exprt::operandst &indices() const
  {
    return op2().operands();
  }

  exprt::operandst &indices()
  {
    return op2().operands();
  }

  vector_exprt lower() const;
};

template <>
inline bool can_cast_expr<shuffle_vector_exprt>(const exprt &base)
{
  return base.id() == ID_shuffle_vector;
}

inline void validate_expr(const shuffle_vector_exprt &value)
{
  validate_operands(value, 3, "shuffle_vector must have three operands");
}

/// \brief Cast an exprt to a \ref shuffle_vector_exprt
///
/// \a expr must be known to be \ref shuffle_vector_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref shuffle_vector_exprt
inline const shuffle_vector_exprt &to_shuffle_vector_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_shuffle_vector);
  const shuffle_vector_exprt &ret =
    static_cast<const shuffle_vector_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_shuffle_vector_expr(const exprt &)
inline shuffle_vector_exprt &to_shuffle_vector_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_shuffle_vector);
  shuffle_vector_exprt &ret = static_cast<shuffle_vector_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief A Boolean expression returning true, iff the result of performing
/// operation \c kind on operands \c a and \c b in infinite-precision arithmetic
/// cannot be represented in the type of the object that \c result points to (or
/// the type of \c result, if it is not a pointer).
/// If \c result is a pointer, the result of the operation is stored in the
/// object pointed to by \c result.
class side_effect_expr_overflowt : public side_effect_exprt
{
public:
  side_effect_expr_overflowt(
    const irep_idt &kind,
    exprt _lhs,
    exprt _rhs,
    exprt _result,
    const source_locationt &loc)
    : side_effect_exprt(
        "overflow-" + id2string(kind),
        {std::move(_lhs), std::move(_rhs), std::move(_result)},
        bool_typet{},
        loc)
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

  exprt &result()
  {
    return op2();
  }

  const exprt &result() const
  {
    return op2();
  }
};

template <>
inline bool can_cast_expr<side_effect_expr_overflowt>(const exprt &base)
{
  if(base.id() != ID_side_effect)
    return false;

  const irep_idt &statement = to_side_effect_expr(base).get_statement();
  return statement == ID_overflow_plus || statement == ID_overflow_mult ||
         statement == ID_overflow_minus;
}

/// \brief Cast an exprt to a \ref side_effect_expr_overflowt
///
/// \a expr must be known to be \ref side_effect_expr_overflowt.
///
/// \param expr: Source expression
/// \return Object of type \ref side_effect_expr_overflowt
inline const side_effect_expr_overflowt &
to_side_effect_expr_overflow(const exprt &expr)
{
  const auto &side_effect_expr = to_side_effect_expr(expr);
  PRECONDITION(
    side_effect_expr.get_statement() == ID_overflow_plus ||
    side_effect_expr.get_statement() == ID_overflow_mult ||
    side_effect_expr.get_statement() == ID_overflow_minus);
  return static_cast<const side_effect_expr_overflowt &>(side_effect_expr);
}

/// \copydoc to_side_effect_expr_overflow(const exprt &)
inline side_effect_expr_overflowt &to_side_effect_expr_overflow(exprt &expr)
{
  auto &side_effect_expr = to_side_effect_expr(expr);
  PRECONDITION(
    side_effect_expr.get_statement() == ID_overflow_plus ||
    side_effect_expr.get_statement() == ID_overflow_mult ||
    side_effect_expr.get_statement() == ID_overflow_minus);
  return static_cast<side_effect_expr_overflowt &>(side_effect_expr);
}

/// \brief A class for an expression that indicates the pre-function-call
/// value of an expression passed as a parameter to a function
class old_exprt : public unary_exprt
{
public:
  explicit old_exprt(exprt variable) : unary_exprt(ID_old, std::move(variable))
  {
  }

  const exprt &expression() const
  {
    return op0();
  }
};

inline const old_exprt &to_old_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_old);
  auto &ret = static_cast<const old_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

#endif // CPROVER_ANSI_C_C_EXPR_H
