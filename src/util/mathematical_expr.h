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
  DEPRECATED(SINCE(2019, 1, 12, "use transt(op0, op1, op2) instead"))
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

template <>
inline bool can_cast_expr<transt>(const exprt &base)
{
  return base.id() == ID_trans;
}

inline void validate_expr(const transt &value)
{
  validate_operands(value, 3, "Transition systems must have three operands");
}

/// Cast an exprt to a \ref transt
/// \a expr must be known to be \ref transt.
/// \param expr: Source expression
/// \return Object of type \ref transt
inline const transt &to_trans_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_trans);
  const transt &ret = static_cast<const transt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_trans_expr(const exprt &)
inline transt &to_trans_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_trans);
  transt &ret = static_cast<transt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Exponentiation
class power_exprt : public binary_exprt
{
public:
  power_exprt(const exprt &_base, const exprt &_exp)
    : binary_exprt(_base, ID_power, _exp)
  {
  }
};

template <>
inline bool can_cast_expr<power_exprt>(const exprt &base)
{
  return base.id() == ID_power;
}

inline void validate_expr(const power_exprt &value)
{
  validate_operands(value, 2, "Power must have two operands");
}

/// \brief Cast an exprt to a \ref power_exprt
///
/// \a expr must be known to be \ref power_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref power_exprt
inline const power_exprt &to_power_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_power);
  const power_exprt &ret = static_cast<const power_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_power_expr(const exprt &)
inline power_exprt &to_power_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_power);
  power_exprt &ret = static_cast<power_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Falling factorial power
class factorial_power_exprt : public binary_exprt
{
public:
  factorial_power_exprt(const exprt &_base, const exprt &_exp)
    : binary_exprt(_base, ID_factorial_power, _exp)
  {
  }
};

template <>
inline bool can_cast_expr<factorial_power_exprt>(const exprt &base)
{
  return base.id() == ID_factorial_power;
}

inline void validate_expr(const factorial_power_exprt &value)
{
  validate_operands(value, 2, "Factorial power must have two operands");
}

/// \brief Cast an exprt to a \ref factorial_power_exprt
///
/// \a expr must be known to be \ref factorial_power_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref factorial_power_exprt
inline const factorial_power_exprt &to_factorial_power_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_factorial_power);
  const factorial_power_exprt &ret =
    static_cast<const factorial_power_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_factorial_power_expr(const exprt &)
inline factorial_power_exprt &to_factorial_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_factorial_power);
  factorial_power_exprt &ret = static_cast<factorial_power_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class tuple_exprt : public multi_ary_exprt
{
public:
  explicit tuple_exprt(exprt::operandst operands)
    : multi_ary_exprt(ID_tuple, std::move(operands), typet())
  {
  }
};

/// \brief Application of (mathematical) function
class function_application_exprt : public binary_exprt
{
public:
  using argumentst = exprt::operandst;

  DEPRECATED(
    SINCE(2019, 3, 3, "use function_application_exprt(fkt, arg) instead"))
  function_application_exprt(
    const symbol_exprt &_function,
    const argumentst &_arguments,
    const typet &_type)
    : binary_exprt(
        _function,
        ID_function_application,
        tuple_exprt(_arguments),
        _type)
  {
  }

  function_application_exprt(const exprt &_function, argumentst _arguments);

  exprt &function()
  {
    return op0();
  }

  const exprt &function() const
  {
    return op0();
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

template <>
inline bool can_cast_expr<function_application_exprt>(const exprt &base)
{
  return base.id() == ID_function_application;
}

inline void validate_expr(const function_application_exprt &value)
{
  validate_operands(value, 2, "Function application must have two operands");
}

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
  const function_application_exprt &ret =
    static_cast<const function_application_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_function_application_expr(const exprt &)
inline function_application_exprt &to_function_application_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_function_application);
  function_application_exprt &ret =
    static_cast<function_application_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief A base class for quantifier expressions
class quantifier_exprt : public binding_exprt
{
public:
  /// constructor for single variable
  quantifier_exprt(irep_idt _id, symbol_exprt _symbol, exprt _where)
    : binding_exprt(_id, {std::move(_symbol)}, std::move(_where), bool_typet())
  {
  }

  /// constructor for multiple variables
  quantifier_exprt(irep_idt _id, const variablest &_variables, exprt _where)
    : binding_exprt(_id, _variables, std::move(_where), bool_typet())
  {
  }

  // for the special case of one variable
  symbol_exprt &symbol()
  {
    auto &variables = this->variables();
    PRECONDITION(variables.size() == 1);
    return variables.front();
  }

  // for the special case of one variable
  const symbol_exprt &symbol() const
  {
    auto &variables = this->variables();
    PRECONDITION(variables.size() == 1);
    return variables.front();
  }
};

template <>
inline bool can_cast_expr<quantifier_exprt>(const exprt &base)
{
  return base.id() == ID_forall || base.id() == ID_exists;
}

inline void validate_expr(const quantifier_exprt &value)
{
  validate_operands(value, 2, "quantifier expressions must have two operands");
  for(auto &op : value.variables())
    DATA_INVARIANT(
      op.id() == ID_symbol, "quantified variable shall be a symbol");
}

/// \brief Cast an exprt to a \ref quantifier_exprt
///
/// \a expr must be known to be \ref quantifier_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref quantifier_exprt
inline const quantifier_exprt &to_quantifier_expr(const exprt &expr)
{
  PRECONDITION(can_cast_expr<quantifier_exprt>(expr));
  const quantifier_exprt &ret = static_cast<const quantifier_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_quantifier_expr(const exprt &)
inline quantifier_exprt &to_quantifier_expr(exprt &expr)
{
  PRECONDITION(can_cast_expr<quantifier_exprt>(expr));
  quantifier_exprt &ret = static_cast<quantifier_exprt &>(expr);
  validate_expr(ret);
  return ret;
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

inline const forall_exprt &to_forall_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_forall);
  const forall_exprt &ret = static_cast<const forall_exprt &>(expr);
  validate_expr(static_cast<const quantifier_exprt &>(ret));
  return ret;
}

inline forall_exprt &to_forall_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_forall);
  forall_exprt &ret = static_cast<forall_exprt &>(expr);
  validate_expr(static_cast<const quantifier_exprt &>(ret));
  return ret;
}

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
  const exists_exprt &ret = static_cast<const exists_exprt &>(expr);
  validate_expr(static_cast<const quantifier_exprt &>(ret));
  return ret;
}

inline exists_exprt &to_exists_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_exists);
  exists_exprt &ret = static_cast<exists_exprt &>(expr);
  validate_expr(static_cast<const quantifier_exprt &>(ret));
  return ret;
}

#endif // CPROVER_UTIL_MATHEMATICAL_EXPR_H
