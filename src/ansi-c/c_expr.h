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

#endif // CPROVER_ANSI_C_C_EXPR_H
