/*******************************************************************\

Module: API to expression classes for 'mathematical' expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_MATHEMATICAL_EXPR_H
#define CPROVER_UTIL_MATHEMATICAL_EXPR_H

/// \file util/mathematical_expr.h
/// API to expression classes for 'mathematical' expressions

#include "std_expr.h"

/// Transition system, consisting of state invariant, initial state predicate,
/// and transition predicate.
class transt : public ternary_exprt
{
public:
  DEPRECATED("use transt(op0, op1, op2) instead")
  transt() : ternary_exprt(ID_trans)
  {
  }

  transt(
    const irep_idt &_id,
    const exprt &_op0,
    const exprt &_op1,
    const exprt &_op2,
    const typet &_type)
    : ternary_exprt(_id, _op0, _op1, _op2, _type)
  {
  }

  exprt &invar()
  {
    return op0();
  }
  exprt &init()
  {
    return op1();
  }
  exprt &trans()
  {
    return op2();
  }

  const exprt &invar() const
  {
    return op0();
  }
  const exprt &init() const
  {
    return op1();
  }
  const exprt &trans() const
  {
    return op2();
  }
};

/// Cast an exprt to a \ref transt
/// \a expr must be known to be \ref transt.
/// \param expr: Source expression
/// \return Object of type \ref transt
inline const transt &to_trans_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_trans);
  DATA_INVARIANT(
    expr.operands().size() == 3, "Transition systems must have three operands");
  return static_cast<const transt &>(expr);
}

/// \copydoc to_trans_expr(const exprt &)
inline transt &to_trans_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_trans);
  DATA_INVARIANT(
    expr.operands().size() == 3, "Transition systems must have three operands");
  return static_cast<transt &>(expr);
}

template <>
inline bool can_cast_expr<transt>(const exprt &base)
{
  return base.id() == ID_trans;
}
inline void validate_expr(const transt &value)
{
  validate_operands(value, 3, "Transition systems must have three operands");
}

/// \brief Exponentiation
class power_exprt : public binary_exprt
{
public:
  DEPRECATED("use power_exprt(lhs, rhs) instead")
  power_exprt() : binary_exprt(ID_power)
  {
  }

  power_exprt(const exprt &_base, const exprt &_exp)
    : binary_exprt(_base, ID_power, _exp)
  {
  }
};

/// \brief Cast an exprt to a \ref power_exprt
///
/// \a expr must be known to be \ref power_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref power_exprt
inline const power_exprt &to_power_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_power);
  DATA_INVARIANT(expr.operands().size() == 2, "Power must have two operands");
  return static_cast<const power_exprt &>(expr);
}

/// \copydoc to_power_expr(const exprt &)
inline power_exprt &to_power_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_power);
  DATA_INVARIANT(expr.operands().size() == 2, "Power must have two operands");
  return static_cast<power_exprt &>(expr);
}

template <>
inline bool can_cast_expr<power_exprt>(const exprt &base)
{
  return base.id() == ID_power;
}
inline void validate_expr(const power_exprt &value)
{
  validate_operands(value, 2, "Power must have two operands");
}

/// \brief Falling factorial power
class factorial_power_exprt : public binary_exprt
{
public:
  DEPRECATED("use factorial_power_exprt(lhs, rhs) instead")
  factorial_power_exprt() : binary_exprt(ID_factorial_power)
  {
  }

  factorial_power_exprt(const exprt &_base, const exprt &_exp)
    : binary_exprt(_base, ID_factorial_power, _exp)
  {
  }
};

/// \brief Cast an exprt to a \ref factorial_power_exprt
///
/// \a expr must be known to be \ref factorial_power_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref factorial_power_exprt
inline const factorial_power_exprt &to_factorial_power_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_factorial_power);
  DATA_INVARIANT(
    expr.operands().size() == 2, "Factorial power must have two operands");
  return static_cast<const factorial_power_exprt &>(expr);
}

/// \copydoc to_factorial_power_expr(const exprt &)
inline factorial_power_exprt &to_factorial_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_factorial_power);
  DATA_INVARIANT(
    expr.operands().size() == 2, "Factorial power must have two operands");
  return static_cast<factorial_power_exprt &>(expr);
}

template <>
inline bool can_cast_expr<factorial_power_exprt>(const exprt &base)
{
  return base.id() == ID_factorial_power;
}
inline void validate_expr(const factorial_power_exprt &value)
{
  validate_operands(value, 2, "Factorial power must have two operands");
}

/// \brief Application of (mathematical) function
class function_application_exprt : public binary_exprt
{
public:
  using argumentst = exprt::operandst;

  function_application_exprt(
    const symbol_exprt &_function,
    const argumentst &_arguments,
    const typet &_type)
    : binary_exprt(_function, ID_function_application, exprt(), _type)
  {
    arguments() = _arguments;
  }

  symbol_exprt &function()
  {
    return static_cast<symbol_exprt &>(op0());
  }

  const symbol_exprt &function() const
  {
    return static_cast<const symbol_exprt &>(op0());
  }

  argumentst &arguments()
  {
    return op1().operands();
  }

  const argumentst &arguments() const
  {
    return op1().operands();
  }
};

/// \brief Cast an exprt to a \ref function_application_exprt
///
/// \a expr must be known to be \ref function_application_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref function_application_exprt
inline const function_application_exprt &
to_function_application_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_function_application);
  DATA_INVARIANT(
    expr.operands().size() == 2, "Function application must have two operands");
  return static_cast<const function_application_exprt &>(expr);
}

/// \copydoc to_function_application_expr(const exprt &)
inline function_application_exprt &to_function_application_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_function_application);
  DATA_INVARIANT(
    expr.operands().size() == 2, "Function application must have two operands");
  return static_cast<function_application_exprt &>(expr);
}

template <>
inline bool can_cast_expr<function_application_exprt>(const exprt &base)
{
  return base.id() == ID_function_application;
}
inline void validate_expr(const function_application_exprt &value)
{
  validate_operands(value, 2, "Function application must have two operands");
}

/// \brief A base class for quantifier expressions
class quantifier_exprt : public binary_predicate_exprt
{
public:
  quantifier_exprt(
    const irep_idt &_id,
    const symbol_exprt &_symbol,
    const exprt &_where)
    : binary_predicate_exprt(_symbol, _id, _where)
  {
  }

  symbol_exprt &symbol()
  {
    return static_cast<symbol_exprt &>(op0());
  }

  const symbol_exprt &symbol() const
  {
    return static_cast<const symbol_exprt &>(op0());
  }

  exprt &where()
  {
    return op1();
  }

  const exprt &where() const
  {
    return op1();
  }
};

/// \brief Cast an exprt to a \ref quantifier_exprt
///
/// \a expr must be known to be \ref quantifier_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref quantifier_exprt
inline const quantifier_exprt &to_quantifier_expr(const exprt &expr)
{
  DATA_INVARIANT(
    expr.operands().size() == 2,
    "quantifier expressions must have two operands");
  DATA_INVARIANT(
    expr.op0().id() == ID_symbol, "quantified variable shall be a symbol");
  return static_cast<const quantifier_exprt &>(expr);
}

/// \copydoc to_quantifier_expr(const exprt &)
inline quantifier_exprt &to_quantifier_expr(exprt &expr)
{
  DATA_INVARIANT(
    expr.operands().size() == 2,
    "quantifier expressions must have two operands");
  DATA_INVARIANT(
    expr.op0().id() == ID_symbol, "quantified variable shall be a symbol");
  return static_cast<quantifier_exprt &>(expr);
}

template <>
inline bool can_cast_expr<quantifier_exprt>(const exprt &base)
{
  return base.id() == ID_forall || base.id() == ID_exists;
}

inline void validate_expr(const quantifier_exprt &value)
{
  validate_operands(value, 2, "quantifier expressions must have two operands");
}

/// \brief A forall expression
class forall_exprt : public quantifier_exprt
{
public:
  forall_exprt(const symbol_exprt &_symbol, const exprt &_where)
    : quantifier_exprt(ID_forall, _symbol, _where)
  {
  }
};

/// \brief An exists expression
class exists_exprt : public quantifier_exprt
{
public:
  exists_exprt(const symbol_exprt &_symbol, const exprt &_where)
    : quantifier_exprt(ID_exists, _symbol, _where)
  {
  }
};

inline const exists_exprt &to_exists_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_exists);
  DATA_INVARIANT(
    expr.operands().size() == 2,
    "exists expressions have exactly two operands");
  return static_cast<const exists_exprt &>(expr);
}

inline exists_exprt &to_exists_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_exists);
  DATA_INVARIANT(
    expr.operands().size() == 2,
    "exists expressions have exactly two operands");
  return static_cast<exists_exprt &>(expr);
}

#endif // CPROVER_UTIL_MATHEMATICAL_EXPR_H
