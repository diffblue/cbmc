/*******************************************************************\

Module: API to expression classes

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_STD_EXPR_H
#define CPROVER_UTIL_STD_EXPR_H

/// \file util/std_expr.h
/// API to expression classes

#include "expr_cast.h"
#include "invariant.h"
#include "std_types.h"

/// An expression without operands
class nullary_exprt : public expr_protectedt
{
public:
  nullary_exprt(const irep_idt &_id, typet _type)
    : expr_protectedt(_id, std::move(_type))
  {
  }

  /// remove all operand methods
  operandst &operands() = delete;
  const operandst &operands() const = delete;

  const exprt &op0() const = delete;
  exprt &op0() = delete;
  const exprt &op1() const = delete;
  exprt &op1() = delete;
  const exprt &op2() const = delete;
  exprt &op2() = delete;
  const exprt &op3() const = delete;
  exprt &op3() = delete;

  void copy_to_operands(const exprt &expr) = delete;
  void copy_to_operands(const exprt &, const exprt &) = delete;
  void copy_to_operands(const exprt &, const exprt &, const exprt &) = delete;
};

/// An expression with three operands
class ternary_exprt : public expr_protectedt
{
public:
  // constructor
  ternary_exprt(
    const irep_idt &_id,
    exprt _op0,
    exprt _op1,
    exprt _op2,
    typet _type)
    : expr_protectedt(
        _id,
        std::move(_type),
        {std::move(_op0), std::move(_op1), std::move(_op2)})
  {
  }

  // make op0 to op2 public
  using exprt::op0;
  using exprt::op1;
  using exprt::op2;

  const exprt &op3() const = delete;
  exprt &op3() = delete;

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm,
      expr.operands().size() == 3,
      "ternary expression must have three operands");
  }

  static void validate(
    const exprt &expr,
    const namespacet &,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    check(expr, vm);
  }
};

/// \brief Cast an exprt to a \ref ternary_exprt
///
/// \a expr must be known to be \ref ternary_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref ternary_exprt
inline const ternary_exprt &to_ternary_expr(const exprt &expr)
{
  ternary_exprt::check(expr);
  return static_cast<const ternary_exprt &>(expr);
}

/// \copydoc to_ternary_expr(const exprt &)
inline ternary_exprt &to_ternary_expr(exprt &expr)
{
  ternary_exprt::check(expr);
  return static_cast<ternary_exprt &>(expr);
}

/// Expression to hold a symbol (variable)
class symbol_exprt : public nullary_exprt
{
public:
  /// \param type: Type of symbol
  explicit symbol_exprt(typet type) : nullary_exprt(ID_symbol, std::move(type))
  {
  }

  /// \param identifier: Name of symbol
  /// \param type: Type of symbol
  symbol_exprt(const irep_idt &identifier, typet type)
    : nullary_exprt(ID_symbol, std::move(type))
  {
    set_identifier(identifier);
  }

  /// Generate a symbol_exprt without a proper type. Use if, and only if, the
  /// type either cannot be determined just yet (such as during type checking)
  /// or when the type truly is immaterial. The latter case may better be dealt
  /// with by using just an irep_idt, and not a symbol_exprt.
  static symbol_exprt typeless(const irep_idt &id)
  {
    return symbol_exprt(id, typet());
  }

  void set_identifier(const irep_idt &identifier)
  {
    set(ID_identifier, identifier);
  }

  const irep_idt &get_identifier() const
  {
    return get(ID_identifier);
  }
};

// NOLINTNEXTLINE(readability/namespace)
namespace std
{
template <>
// NOLINTNEXTLINE(readability/identifiers)
struct hash<::symbol_exprt>
{
  size_t operator()(const ::symbol_exprt &sym)
  {
    return irep_id_hash()(sym.get_identifier());
  }
};
} // namespace std

/// Expression to hold a symbol (variable) with extra accessors to
/// ID_c_static_lifetime and ID_C_thread_local
class decorated_symbol_exprt:public symbol_exprt
{
public:
  /// \param identifier: Name of symbol
  /// \param type: Type of symbol
  decorated_symbol_exprt(const irep_idt &identifier, typet type)
    : symbol_exprt(identifier, std::move(type))
  {
  }

  bool is_static_lifetime() const
  {
    return get_bool(ID_C_static_lifetime);
  }

  void set_static_lifetime()
  {
    return set(ID_C_static_lifetime, true);
  }

  void clear_static_lifetime()
  {
    remove(ID_C_static_lifetime);
  }

  bool is_thread_local() const
  {
    return get_bool(ID_C_thread_local);
  }

  void set_thread_local()
  {
    return set(ID_C_thread_local, true);
  }

  void clear_thread_local()
  {
    remove(ID_C_thread_local);
  }
};

template <>
inline bool can_cast_expr<symbol_exprt>(const exprt &base)
{
  return base.id() == ID_symbol;
}

inline void validate_expr(const symbol_exprt &value)
{
  validate_operands(value, 0, "Symbols must not have operands");
}

/// \brief Cast an exprt to a \ref symbol_exprt
///
/// \a expr must be known to be \ref symbol_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref symbol_exprt
inline const symbol_exprt &to_symbol_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_symbol);
  const symbol_exprt &ret = static_cast<const symbol_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_symbol_expr(const exprt &)
inline symbol_exprt &to_symbol_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_symbol);
  symbol_exprt &ret = static_cast<symbol_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Expression to hold a nondeterministic choice
class nondet_symbol_exprt : public nullary_exprt
{
public:
  /// \param identifier: Name of symbol
  /// \param type: Type of symbol
  nondet_symbol_exprt(const irep_idt &identifier, typet type)
    : nullary_exprt(ID_nondet_symbol, std::move(type))
  {
    set_identifier(identifier);
  }

  /// \param identifier: name of symbol
  /// \param type: type of symbol
  /// \param location: location from which the symbol originate
  nondet_symbol_exprt(
    irep_idt identifier,
    typet type,
    source_locationt location)
    : nullary_exprt(ID_nondet_symbol, std::move(type))
  {
    set_identifier(std::move(identifier));
    add_source_location() = std::move(location);
  }

  void set_identifier(const irep_idt &identifier)
  {
    set(ID_identifier, identifier);
  }

  const irep_idt &get_identifier() const
  {
    return get(ID_identifier);
  }
};

template <>
inline bool can_cast_expr<nondet_symbol_exprt>(const exprt &base)
{
  return base.id() == ID_nondet_symbol;
}

inline void validate_expr(const nondet_symbol_exprt &value)
{
  validate_operands(value, 0, "Symbols must not have operands");
}

/// \brief Cast an exprt to a \ref nondet_symbol_exprt
///
/// \a expr must be known to be \ref nondet_symbol_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref nondet_symbol_exprt
inline const nondet_symbol_exprt &to_nondet_symbol_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_nondet_symbol);
  const nondet_symbol_exprt &ret =
    static_cast<const nondet_symbol_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_nondet_symbol_expr(const exprt &)
inline nondet_symbol_exprt &to_nondet_symbol_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_symbol);
  nondet_symbol_exprt &ret = static_cast<nondet_symbol_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Generic base class for unary expressions
class unary_exprt : public expr_protectedt
{
public:
  unary_exprt(const irep_idt &_id, const exprt &_op)
    : expr_protectedt(_id, _op.type(), {_op})
  {
  }

  unary_exprt(const irep_idt &_id, exprt _op, typet _type)
    : expr_protectedt(_id, std::move(_type), {std::move(_op)})
  {
  }

  const exprt &op() const
  {
    return op0();
  }

  exprt &op()
  {
    return op0();
  }

  const exprt &op1() const = delete;
  exprt &op1() = delete;
  const exprt &op2() const = delete;
  exprt &op2() = delete;
  const exprt &op3() const = delete;
  exprt &op3() = delete;
};

template <>
inline bool can_cast_expr<unary_exprt>(const exprt &base)
{
  return base.operands().size() == 1;
}

inline void validate_expr(const unary_exprt &value)
{
  validate_operands(value, 1, "Unary expressions must have one operand");
}

/// \brief Cast an exprt to a \ref unary_exprt
///
/// \a expr must be known to be \ref unary_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref unary_exprt
inline const unary_exprt &to_unary_expr(const exprt &expr)
{
  const unary_exprt &ret = static_cast<const unary_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_unary_expr(const exprt &)
inline unary_exprt &to_unary_expr(exprt &expr)
{
  unary_exprt &ret = static_cast<unary_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Absolute value
class abs_exprt:public unary_exprt
{
public:
  explicit abs_exprt(exprt _op) : unary_exprt(ID_abs, std::move(_op))
  {
  }
};

template <>
inline bool can_cast_expr<abs_exprt>(const exprt &base)
{
  return base.id() == ID_abs;
}

inline void validate_expr(const abs_exprt &value)
{
  validate_operands(value, 1, "Absolute value must have one operand");
}

/// \brief Cast an exprt to a \ref abs_exprt
///
/// \a expr must be known to be \ref abs_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref abs_exprt
inline const abs_exprt &to_abs_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_abs);
  const abs_exprt &ret = static_cast<const abs_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_abs_expr(const exprt &)
inline abs_exprt &to_abs_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_abs);
  abs_exprt &ret = static_cast<abs_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief The unary minus expression
class unary_minus_exprt:public unary_exprt
{
public:
  unary_minus_exprt(exprt _op, typet _type)
    : unary_exprt(ID_unary_minus, std::move(_op), std::move(_type))
  {
  }

  explicit unary_minus_exprt(exprt _op)
    : unary_exprt(ID_unary_minus, std::move(_op))
  {
  }
};

template <>
inline bool can_cast_expr<unary_minus_exprt>(const exprt &base)
{
  return base.id() == ID_unary_minus;
}

inline void validate_expr(const unary_minus_exprt &value)
{
  validate_operands(value, 1, "Unary minus must have one operand");
}

/// \brief Cast an exprt to a \ref unary_minus_exprt
///
/// \a expr must be known to be \ref unary_minus_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref unary_minus_exprt
inline const unary_minus_exprt &to_unary_minus_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_unary_minus);
  const unary_minus_exprt &ret = static_cast<const unary_minus_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_unary_minus_expr(const exprt &)
inline unary_minus_exprt &to_unary_minus_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_unary_minus);
  unary_minus_exprt &ret = static_cast<unary_minus_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief The unary plus expression
class unary_plus_exprt : public unary_exprt
{
public:
  explicit unary_plus_exprt(exprt op)
    : unary_exprt(ID_unary_plus, std::move(op))
  {
  }
};

template <>
inline bool can_cast_expr<unary_plus_exprt>(const exprt &base)
{
  return base.id() == ID_unary_plus;
}

inline void validate_expr(const unary_plus_exprt &value)
{
  validate_operands(value, 1, "unary plus must have one operand");
}

/// \brief Cast an exprt to a \ref unary_plus_exprt
///
/// \a expr must be known to be \ref unary_plus_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref unary_plus_exprt
inline const unary_plus_exprt &to_unary_plus_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_unary_plus);
  const unary_plus_exprt &ret = static_cast<const unary_plus_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_unary_minus_expr(const exprt &)
inline unary_plus_exprt &to_unary_plus_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_unary_plus);
  unary_plus_exprt &ret = static_cast<unary_plus_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief A base class for expressions that are predicates,
///   i.e., Boolean-typed.
class predicate_exprt : public expr_protectedt
{
public:
  explicit predicate_exprt(const irep_idt &_id)
    : expr_protectedt(_id, bool_typet())
  {
  }
};

/// \brief A base class for expressions that are predicates,
///   i.e., Boolean-typed, and that take exactly one argument.
class unary_predicate_exprt:public unary_exprt
{
public:
  unary_predicate_exprt(const irep_idt &_id, exprt _op)
    : unary_exprt(_id, std::move(_op), bool_typet())
  {
  }
};

/// \brief Sign of an expression
/// Predicate is true if \a _op is negative, false otherwise.
class sign_exprt:public unary_predicate_exprt
{
public:
  explicit sign_exprt(exprt _op)
    : unary_predicate_exprt(ID_sign, std::move(_op))
  {
  }
};

template <>
inline bool can_cast_expr<sign_exprt>(const exprt &base)
{
  return base.id() == ID_sign;
}

inline void validate_expr(const sign_exprt &expr)
{
  validate_operands(expr, 1, "sign expression must have one operand");
}

/// \brief Cast an exprt to a \ref sign_exprt
///
/// \a expr must be known to be a \ref sign_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref sign_exprt
inline const sign_exprt &to_sign_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sign);
  const sign_exprt &ret = static_cast<const sign_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_sign_expr(const exprt &)
inline sign_exprt &to_sign_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sign);
  sign_exprt &ret = static_cast<sign_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief A base class for binary expressions
class binary_exprt : public expr_protectedt
{
public:
  binary_exprt(const exprt &_lhs, const irep_idt &_id, exprt _rhs)
    : expr_protectedt(_id, _lhs.type(), {_lhs, std::move(_rhs)})
  {
  }

  binary_exprt(exprt _lhs, const irep_idt &_id, exprt _rhs, typet _type)
    : expr_protectedt(_id, std::move(_type), {std::move(_lhs), std::move(_rhs)})
  {
  }

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm,
      expr.operands().size() == 2,
      "binary expression must have two operands");
  }

  static void validate(
    const exprt &expr,
    const namespacet &,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    check(expr, vm);
  }

  exprt &lhs()
  {
    return exprt::op0();
  }

  const exprt &lhs() const
  {
    return exprt::op0();
  }

  exprt &rhs()
  {
    return exprt::op1();
  }

  const exprt &rhs() const
  {
    return exprt::op1();
  }

  // make op0 and op1 public
  using exprt::op0;
  using exprt::op1;

  const exprt &op2() const = delete;
  exprt &op2() = delete;
  const exprt &op3() const = delete;
  exprt &op3() = delete;
};

template <>
inline bool can_cast_expr<binary_exprt>(const exprt &base)
{
  return base.operands().size() == 2;
}

inline void validate_expr(const binary_exprt &value)
{
  binary_exprt::check(value);
}

/// \brief Cast an exprt to a \ref binary_exprt
///
/// \a expr must be known to be \ref binary_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref binary_exprt
inline const binary_exprt &to_binary_expr(const exprt &expr)
{
  binary_exprt::check(expr);
  return static_cast<const binary_exprt &>(expr);
}

/// \copydoc to_binary_expr(const exprt &)
inline binary_exprt &to_binary_expr(exprt &expr)
{
  binary_exprt::check(expr);
  return static_cast<binary_exprt &>(expr);
}

/// \brief A base class for expressions that are predicates,
///   i.e., Boolean-typed, and that take exactly two arguments.
class binary_predicate_exprt:public binary_exprt
{
public:
  binary_predicate_exprt(exprt _op0, const irep_idt &_id, exprt _op1)
    : binary_exprt(std::move(_op0), _id, std::move(_op1), bool_typet())
  {
  }

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    binary_exprt::check(expr, vm);
  }

  static void validate(
    const exprt &expr,
    const namespacet &ns,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    binary_exprt::validate(expr, ns, vm);

    DATA_CHECK(
      vm,
      expr.type().id() == ID_bool,
      "result of binary predicate expression should be of type bool");
  }
};

/// \brief A base class for relations, i.e., binary predicates whose
/// two operands have the same type
class binary_relation_exprt:public binary_predicate_exprt
{
public:
  binary_relation_exprt(exprt _lhs, const irep_idt &_id, exprt _rhs)
    : binary_predicate_exprt(std::move(_lhs), _id, std::move(_rhs))
  {
  }

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    binary_predicate_exprt::check(expr, vm);
  }

  static void validate(
    const exprt &expr,
    const namespacet &ns,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    binary_predicate_exprt::validate(expr, ns, vm);

    // we now can safely assume that 'expr' is a binary predicate
    const auto &expr_binary = static_cast<const binary_predicate_exprt &>(expr);

    // check that the types of the operands are the same
    DATA_CHECK(
      vm,
      expr_binary.op0().type() == expr_binary.op1().type(),
      "lhs and rhs of binary relation expression should have same type");
  }
};

template <>
inline bool can_cast_expr<binary_relation_exprt>(const exprt &base)
{
  return can_cast_expr<binary_exprt>(base);
}

inline void validate_expr(const binary_relation_exprt &value)
{
  binary_relation_exprt::check(value);
}

/// \brief Binary greater than operator expression.
class greater_than_exprt : public binary_relation_exprt
{
public:
  greater_than_exprt(exprt _lhs, exprt _rhs)
    : binary_relation_exprt{std::move(_lhs), ID_gt, std::move(_rhs)}
  {
  }
};

template <>
inline bool can_cast_expr<greater_than_exprt>(const exprt &base)
{
  return base.id() == ID_gt;
}

inline void validate_expr(const greater_than_exprt &value)
{
  binary_relation_exprt::check(value);
}

/// \brief Binary greater than or equal operator expression.
class greater_than_or_equal_exprt : public binary_relation_exprt
{
public:
  greater_than_or_equal_exprt(exprt _lhs, exprt _rhs)
    : binary_relation_exprt{std::move(_lhs), ID_ge, std::move(_rhs)}
  {
  }
};

template <>
inline bool can_cast_expr<greater_than_or_equal_exprt>(const exprt &base)
{
  return base.id() == ID_ge;
}

inline void validate_expr(const greater_than_or_equal_exprt &value)
{
  binary_relation_exprt::check(value);
}

/// \brief Binary less than operator expression.
class less_than_exprt : public binary_relation_exprt
{
public:
  less_than_exprt(exprt _lhs, exprt _rhs)
    : binary_relation_exprt{std::move(_lhs), ID_lt, std::move(_rhs)}
  {
  }
};

template <>
inline bool can_cast_expr<less_than_exprt>(const exprt &base)
{
  return base.id() == ID_lt;
}

inline void validate_expr(const less_than_exprt &value)
{
  binary_relation_exprt::check(value);
}

/// \brief Binary less than or equal operator expression.
class less_than_or_equal_exprt : public binary_relation_exprt
{
public:
  less_than_or_equal_exprt(exprt _lhs, exprt _rhs)
    : binary_relation_exprt{std::move(_lhs), ID_le, std::move(_rhs)}
  {
  }
};

template <>
inline bool can_cast_expr<less_than_or_equal_exprt>(const exprt &base)
{
  return base.id() == ID_le;
}

inline void validate_expr(const less_than_or_equal_exprt &value)
{
  binary_relation_exprt::check(value);
}

/// \brief Cast an exprt to a \ref binary_relation_exprt
///
/// \a expr must be known to be \ref binary_relation_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref binary_relation_exprt
inline const binary_relation_exprt &to_binary_relation_expr(const exprt &expr)
{
  binary_relation_exprt::check(expr);
  return static_cast<const binary_relation_exprt &>(expr);
}

/// \copydoc to_binary_relation_expr(const exprt &)
inline binary_relation_exprt &to_binary_relation_expr(exprt &expr)
{
  binary_relation_exprt::check(expr);
  return static_cast<binary_relation_exprt &>(expr);
}


/// \brief A base class for multi-ary expressions
/// Associativity is not specified.
class multi_ary_exprt : public expr_protectedt
{
public:
  multi_ary_exprt(const irep_idt &_id, operandst _operands, typet _type)
    : expr_protectedt(_id, std::move(_type))
  {
    operands() = std::move(_operands);
  }

  multi_ary_exprt(const exprt &_lhs, const irep_idt &_id, exprt _rhs)
    : expr_protectedt(_id, _lhs.type(), {_lhs, std::move(_rhs)})
  {
  }

  multi_ary_exprt(exprt _lhs, const irep_idt &_id, exprt _rhs, typet _type)
    : expr_protectedt(_id, std::move(_type), {std::move(_lhs), std::move(_rhs)})
  {
  }

  // In contrast to exprt::opX, the methods
  // below check the size.
  exprt &op0()
  {
    PRECONDITION(operands().size() >= 1);
    return operands().front();
  }

  exprt &op1()
  {
    PRECONDITION(operands().size() >= 2);
    return operands()[1];
  }

  exprt &op2()
  {
    PRECONDITION(operands().size() >= 3);
    return operands()[2];
  }

  exprt &op3()
  {
    PRECONDITION(operands().size() >= 4);
    return operands()[3];
  }

  const exprt &op0() const
  {
    PRECONDITION(operands().size() >= 1);
    return operands().front();
  }

  const exprt &op1() const
  {
    PRECONDITION(operands().size() >= 2);
    return operands()[1];
  }

  const exprt &op2() const
  {
    PRECONDITION(operands().size() >= 3);
    return operands()[2];
  }

  const exprt &op3() const
  {
    PRECONDITION(operands().size() >= 4);
    return operands()[3];
  }
};

/// \brief Cast an exprt to a \ref multi_ary_exprt
///
/// \a expr must be known to be \ref multi_ary_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref multi_ary_exprt
inline const multi_ary_exprt &to_multi_ary_expr(const exprt &expr)
{
  return static_cast<const multi_ary_exprt &>(expr);
}

/// \copydoc to_multi_ary_expr(const exprt &)
inline multi_ary_exprt &to_multi_ary_expr(exprt &expr)
{
  return static_cast<multi_ary_exprt &>(expr);
}


/// \brief The plus expression
/// Associativity is not specified.
class plus_exprt:public multi_ary_exprt
{
public:
  plus_exprt(exprt _lhs, exprt _rhs)
    : multi_ary_exprt(std::move(_lhs), ID_plus, std::move(_rhs))
  {
  }

  plus_exprt(exprt _lhs, exprt _rhs, typet _type)
    : multi_ary_exprt(
        std::move(_lhs),
        ID_plus,
        std::move(_rhs),
        std::move(_type))
  {
  }

  plus_exprt(operandst _operands, typet _type)
    : multi_ary_exprt(ID_plus, std::move(_operands), std::move(_type))
  {
  }
};

template <>
inline bool can_cast_expr<plus_exprt>(const exprt &base)
{
  return base.id() == ID_plus;
}

inline void validate_expr(const plus_exprt &value)
{
  validate_operands(value, 2, "Plus must have two or more operands", true);
}

/// \brief Cast an exprt to a \ref plus_exprt
///
/// \a expr must be known to be \ref plus_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref plus_exprt
inline const plus_exprt &to_plus_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_plus);
  const plus_exprt &ret = static_cast<const plus_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_plus_expr(const exprt &)
inline plus_exprt &to_plus_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_plus);
  plus_exprt &ret = static_cast<plus_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Binary minus
class minus_exprt:public binary_exprt
{
public:
  minus_exprt(exprt _lhs, exprt _rhs)
    : binary_exprt(std::move(_lhs), ID_minus, std::move(_rhs))
  {
  }
};

template <>
inline bool can_cast_expr<minus_exprt>(const exprt &base)
{
  return base.id() == ID_minus;
}

inline void validate_expr(const minus_exprt &value)
{
  validate_operands(value, 2, "Minus must have two or more operands", true);
}

/// \brief Cast an exprt to a \ref minus_exprt
///
/// \a expr must be known to be \ref minus_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref minus_exprt
inline const minus_exprt &to_minus_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_minus);
  const minus_exprt &ret = static_cast<const minus_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_minus_expr(const exprt &)
inline minus_exprt &to_minus_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_minus);
  minus_exprt &ret = static_cast<minus_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Binary multiplication
/// Associativity is not specified.
class mult_exprt:public multi_ary_exprt
{
public:
  mult_exprt(exprt _lhs, exprt _rhs)
    : multi_ary_exprt(std::move(_lhs), ID_mult, std::move(_rhs))
  {
  }
};

template <>
inline bool can_cast_expr<mult_exprt>(const exprt &base)
{
  return base.id() == ID_mult;
}

inline void validate_expr(const mult_exprt &value)
{
  validate_operands(value, 2, "Multiply must have two or more operands", true);
}

/// \brief Cast an exprt to a \ref mult_exprt
///
/// \a expr must be known to be \ref mult_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref mult_exprt
inline const mult_exprt &to_mult_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_mult);
  const mult_exprt &ret = static_cast<const mult_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_mult_expr(const exprt &)
inline mult_exprt &to_mult_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_mult);
  mult_exprt &ret = static_cast<mult_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Division
class div_exprt:public binary_exprt
{
public:
  div_exprt(exprt _lhs, exprt _rhs)
    : binary_exprt(std::move(_lhs), ID_div, std::move(_rhs))
  {
  }

  /// The dividend of a division is the number that is being divided
  exprt &dividend()
  {
    return op0();
  }

  /// The dividend of a division is the number that is being divided
  const exprt &dividend() const
  {
    return op0();
  }

  /// The divisor of a division is the number the dividend is being divided by
  exprt &divisor()
  {
    return op1();
  }

  /// The divisor of a division is the number the dividend is being divided by
  const exprt &divisor() const
  {
    return op1();
  }
};

template <>
inline bool can_cast_expr<div_exprt>(const exprt &base)
{
  return base.id() == ID_div;
}

inline void validate_expr(const div_exprt &value)
{
  validate_operands(value, 2, "Divide must have two operands");
}

/// \brief Cast an exprt to a \ref div_exprt
///
/// \a expr must be known to be \ref div_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref div_exprt
inline const div_exprt &to_div_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_div);
  const div_exprt &ret = static_cast<const div_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_div_expr(const exprt &)
inline div_exprt &to_div_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_div);
  div_exprt &ret = static_cast<div_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Modulo defined as lhs-(rhs * truncate(lhs/rhs)).
/// The sign follows the lhs or dividend. This matches C99 and
/// SMT-LIB's bvsrem but differs from the Euclidian definition
/// and from SMT-LIB's bvsmod.
class mod_exprt:public binary_exprt
{
public:
  mod_exprt(exprt _lhs, exprt _rhs)
    : binary_exprt(std::move(_lhs), ID_mod, std::move(_rhs))
  {
  }

  /// The dividend of a division is the number that is being divided
  exprt &dividend()
  {
    return op0();
  }

  /// The dividend of a division is the number that is being divided
  const exprt &dividend() const
  {
    return op0();
  }

  /// The divisor of a division is the number the dividend is being divided by
  exprt &divisor()
  {
    return op1();
  }

  /// The divisor of a division is the number the dividend is being divided by
  const exprt &divisor() const
  {
    return op1();
  }
};

template <>
inline bool can_cast_expr<mod_exprt>(const exprt &base)
{
  return base.id() == ID_mod;
}

inline void validate_expr(const mod_exprt &value)
{
  validate_operands(value, 2, "Modulo must have two operands");
}

/// \brief Cast an exprt to a \ref mod_exprt
///
/// \a expr must be known to be \ref mod_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref mod_exprt
inline const mod_exprt &to_mod_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_mod);
  const mod_exprt &ret = static_cast<const mod_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_mod_expr(const exprt &)
inline mod_exprt &to_mod_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_mod);
  mod_exprt &ret = static_cast<mod_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Boute's Euclidean definition of Modulo -- to match SMT-LIB2
class euclidean_mod_exprt : public binary_exprt
{
public:
  euclidean_mod_exprt(exprt _lhs, exprt _rhs)
    : binary_exprt(std::move(_lhs), ID_euclidean_mod, std::move(_rhs))
  {
  }

  /// The dividend of a division is the number that is being divided
  exprt &dividend()
  {
    return op0();
  }

  /// The dividend of a division is the number that is being divided
  const exprt &dividend() const
  {
    return op0();
  }

  /// The divisor of a division is the number the dividend is being divided by
  exprt &divisor()
  {
    return op1();
  }

  /// The divisor of a division is the number the dividend is being divided by
  const exprt &divisor() const
  {
    return op1();
  }
};

template <>
inline bool can_cast_expr<euclidean_mod_exprt>(const exprt &base)
{
  return base.id() == ID_euclidean_mod;
}

inline void validate_expr(const euclidean_mod_exprt &value)
{
  validate_operands(value, 2, "Modulo must have two operands");
}

/// \brief Cast an exprt to a \ref euclidean_mod_exprt
///
/// \a expr must be known to be \ref euclidean_mod_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref euclidean_mod_exprt
inline const euclidean_mod_exprt &to_euclidean_mod_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_euclidean_mod);
  const euclidean_mod_exprt &ret =
    static_cast<const euclidean_mod_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_euclidean_mod_expr(const exprt &)
inline euclidean_mod_exprt &to_euclidean_mod_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_euclidean_mod);
  euclidean_mod_exprt &ret = static_cast<euclidean_mod_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Equality
class equal_exprt:public binary_relation_exprt
{
public:
  equal_exprt(exprt _lhs, exprt _rhs)
    : binary_relation_exprt(std::move(_lhs), ID_equal, std::move(_rhs))
  {
  }

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    binary_relation_exprt::check(expr, vm);
  }

  static void validate(
    const exprt &expr,
    const namespacet &ns,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    binary_relation_exprt::validate(expr, ns, vm);
  }
};

template <>
inline bool can_cast_expr<equal_exprt>(const exprt &base)
{
  return base.id() == ID_equal;
}

inline void validate_expr(const equal_exprt &value)
{
  equal_exprt::check(value);
}

/// \brief Cast an exprt to an \ref equal_exprt
///
/// \a expr must be known to be \ref equal_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref equal_exprt
inline const equal_exprt &to_equal_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_equal);
  equal_exprt::check(expr);
  return static_cast<const equal_exprt &>(expr);
}

/// \copydoc to_equal_expr(const exprt &)
inline equal_exprt &to_equal_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_equal);
  equal_exprt::check(expr);
  return static_cast<equal_exprt &>(expr);
}


/// \brief Disequality
class notequal_exprt:public binary_relation_exprt
{
public:
  notequal_exprt(exprt _lhs, exprt _rhs)
    : binary_relation_exprt(std::move(_lhs), ID_notequal, std::move(_rhs))
  {
  }
};

template <>
inline bool can_cast_expr<notequal_exprt>(const exprt &base)
{
  return base.id() == ID_notequal;
}

inline void validate_expr(const notequal_exprt &value)
{
  validate_operands(value, 2, "Inequality must have two operands");
}

/// \brief Cast an exprt to an \ref notequal_exprt
///
/// \a expr must be known to be \ref notequal_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref notequal_exprt
inline const notequal_exprt &to_notequal_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_notequal);
  const notequal_exprt &ret = static_cast<const notequal_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_notequal_expr(const exprt &)
inline notequal_exprt &to_notequal_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_notequal);
  notequal_exprt &ret = static_cast<notequal_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Array index operator
class index_exprt:public binary_exprt
{
public:
  // When _array has array_type, the type of _index
  // must be array_type.index_type().
  // This will eventually be enforced using a precondition.
  index_exprt(const exprt &_array, exprt _index)
    : binary_exprt(
        _array,
        ID_index,
        std::move(_index),
        _array.type().has_subtype()
          ? to_type_with_subtype(_array.type()).subtype()
          : typet(ID_nil))
  {
  }

  index_exprt(exprt _array, exprt _index, typet _type)
    : binary_exprt(
        std::move(_array),
        ID_index,
        std::move(_index),
        std::move(_type))
  {
  }

  exprt &array()
  {
    return op0();
  }

  const exprt &array() const
  {
    return op0();
  }

  exprt &index()
  {
    return op1();
  }

  const exprt &index() const
  {
    return op1();
  }
};

template <>
inline bool can_cast_expr<index_exprt>(const exprt &base)
{
  return base.id() == ID_index;
}

inline void validate_expr(const index_exprt &value)
{
  validate_operands(value, 2, "Array index must have two operands");
}

/// \brief Cast an exprt to an \ref index_exprt
///
/// \a expr must be known to be \ref index_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref index_exprt
inline const index_exprt &to_index_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_index);
  const index_exprt &ret = static_cast<const index_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_index_expr(const exprt &)
inline index_exprt &to_index_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_index);
  index_exprt &ret = static_cast<index_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Array constructor from single element
class array_of_exprt:public unary_exprt
{
public:
  explicit array_of_exprt(exprt _what, array_typet _type)
    : unary_exprt(ID_array_of, std::move(_what), std::move(_type))
  {
  }

  const array_typet &type() const
  {
    return static_cast<const array_typet &>(unary_exprt::type());
  }

  array_typet &type()
  {
    return static_cast<array_typet &>(unary_exprt::type());
  }

  exprt &what()
  {
    return op0();
  }

  const exprt &what() const
  {
    return op0();
  }
};

template <>
inline bool can_cast_expr<array_of_exprt>(const exprt &base)
{
  return base.id() == ID_array_of;
}

inline void validate_expr(const array_of_exprt &value)
{
  validate_operands(value, 1, "'Array of' must have one operand");
}

/// \brief Cast an exprt to an \ref array_of_exprt
///
/// \a expr must be known to be \ref array_of_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref array_of_exprt
inline const array_of_exprt &to_array_of_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_array_of);
  const array_of_exprt &ret = static_cast<const array_of_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_array_of_expr(const exprt &)
inline array_of_exprt &to_array_of_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_array_of);
  array_of_exprt &ret = static_cast<array_of_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Array constructor from list of elements
class array_exprt : public multi_ary_exprt
{
public:
  array_exprt(operandst _operands, array_typet _type)
    : multi_ary_exprt(ID_array, std::move(_operands), std::move(_type))
  {
  }

  const array_typet &type() const
  {
    return static_cast<const array_typet &>(multi_ary_exprt::type());
  }

  array_typet &type()
  {
    return static_cast<array_typet &>(multi_ary_exprt::type());
  }
};

template <>
inline bool can_cast_expr<array_exprt>(const exprt &base)
{
  return base.id() == ID_array;
}

/// \brief Cast an exprt to an \ref array_exprt
///
/// \a expr must be known to be \ref array_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref array_exprt
inline const array_exprt &to_array_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_array);
  return static_cast<const array_exprt &>(expr);
}

/// \copydoc to_array_expr(const exprt &)
inline array_exprt &to_array_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_array);
  return static_cast<array_exprt &>(expr);
}

/// Array constructor from a list of index-element pairs
/// Operands are index/value pairs, alternating.
class array_list_exprt : public multi_ary_exprt
{
public:
  array_list_exprt(operandst _operands, array_typet _type)
    : multi_ary_exprt(ID_array_list, std::move(_operands), std::move(_type))
  {
  }

  const array_typet &type() const
  {
    return static_cast<const array_typet &>(multi_ary_exprt::type());
  }

  array_typet &type()
  {
    return static_cast<array_typet &>(multi_ary_exprt::type());
  }

  /// add an index/value pair
  void add(exprt index, exprt value)
  {
    add_to_operands(std::move(index), std::move(value));
  }
};

template <>
inline bool can_cast_expr<array_list_exprt>(const exprt &base)
{
  return base.id() == ID_array_list;
}

inline void validate_expr(const array_list_exprt &value)
{
  PRECONDITION(value.operands().size() % 2 == 0);
}

inline const array_list_exprt &to_array_list_expr(const exprt &expr)
{
  PRECONDITION(can_cast_expr<array_list_exprt>(expr));
  auto &ret = static_cast<const array_list_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

inline array_list_exprt &to_array_list_expr(exprt &expr)
{
  PRECONDITION(can_cast_expr<array_list_exprt>(expr));
  auto &ret = static_cast<array_list_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Vector constructor from list of elements
class vector_exprt : public multi_ary_exprt
{
public:
  vector_exprt(operandst _operands, vector_typet _type)
    : multi_ary_exprt(ID_vector, std::move(_operands), std::move(_type))
  {
  }
};

template <>
inline bool can_cast_expr<vector_exprt>(const exprt &base)
{
  return base.id() == ID_vector;
}

/// \brief Cast an exprt to an \ref vector_exprt
///
/// \a expr must be known to be \ref vector_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref vector_exprt
inline const vector_exprt &to_vector_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_vector);
  return static_cast<const vector_exprt &>(expr);
}

/// \copydoc to_vector_expr(const exprt &)
inline vector_exprt &to_vector_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_vector);
  return static_cast<vector_exprt &>(expr);
}


/// \brief Union constructor from single element
class union_exprt:public unary_exprt
{
public:
  union_exprt(const irep_idt &_component_name, exprt _value, typet _type)
    : unary_exprt(ID_union, std::move(_value), std::move(_type))
  {
    set_component_name(_component_name);
  }

  irep_idt get_component_name() const
  {
    return get(ID_component_name);
  }

  void set_component_name(const irep_idt &component_name)
  {
    set(ID_component_name, component_name);
  }

  std::size_t get_component_number() const
  {
    return get_size_t(ID_component_number);
  }

  void set_component_number(std::size_t component_number)
  {
    set_size_t(ID_component_number, component_number);
  }
};

template <>
inline bool can_cast_expr<union_exprt>(const exprt &base)
{
  return base.id() == ID_union;
}

inline void validate_expr(const union_exprt &value)
{
  validate_operands(value, 1, "Union constructor must have one operand");
}

/// \brief Cast an exprt to a \ref union_exprt
///
/// \a expr must be known to be \ref union_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref union_exprt
inline const union_exprt &to_union_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_union);
  const union_exprt &ret = static_cast<const union_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_union_expr(const exprt &)
inline union_exprt &to_union_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_union);
  union_exprt &ret = static_cast<union_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Union constructor to support unions without any member (a GCC/Clang
/// feature).
class empty_union_exprt : public nullary_exprt
{
public:
  explicit empty_union_exprt(typet _type)
    : nullary_exprt(ID_empty_union, std::move(_type))
  {
  }
};

template <>
inline bool can_cast_expr<empty_union_exprt>(const exprt &base)
{
  return base.id() == ID_empty_union;
}

inline void validate_expr(const empty_union_exprt &value)
{
  validate_operands(
    value, 0, "Empty-union constructor must not have any operand");
}

/// \brief Cast an exprt to an \ref empty_union_exprt
///
/// \a expr must be known to be \ref empty_union_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref empty_union_exprt
inline const empty_union_exprt &to_empty_union_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_empty_union);
  const empty_union_exprt &ret = static_cast<const empty_union_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_empty_union_expr(const exprt &)
inline empty_union_exprt &to_empty_union_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_empty_union);
  empty_union_exprt &ret = static_cast<empty_union_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Struct constructor from list of elements
class struct_exprt : public multi_ary_exprt
{
public:
  struct_exprt(operandst _operands, typet _type)
    : multi_ary_exprt(ID_struct, std::move(_operands), std::move(_type))
  {
  }

  exprt &component(const irep_idt &name, const namespacet &ns);
  const exprt &component(const irep_idt &name, const namespacet &ns) const;
};

template <>
inline bool can_cast_expr<struct_exprt>(const exprt &base)
{
  return base.id() == ID_struct;
}

/// \brief Cast an exprt to a \ref struct_exprt
///
/// \a expr must be known to be \ref struct_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref struct_exprt
inline const struct_exprt &to_struct_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_struct);
  return static_cast<const struct_exprt &>(expr);
}

/// \copydoc to_struct_expr(const exprt &)
inline struct_exprt &to_struct_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_struct);
  return static_cast<struct_exprt &>(expr);
}


/// \brief Complex constructor from a pair of numbers
class complex_exprt:public binary_exprt
{
public:
  complex_exprt(exprt _real, exprt _imag, complex_typet _type)
    : binary_exprt(
        std::move(_real),
        ID_complex,
        std::move(_imag),
        std::move(_type))
  {
  }

  exprt real()
  {
    return op0();
  }

  const exprt &real() const
  {
    return op0();
  }

  exprt imag()
  {
    return op1();
  }

  const exprt &imag() const
  {
    return op1();
  }
};

template <>
inline bool can_cast_expr<complex_exprt>(const exprt &base)
{
  return base.id() == ID_complex;
}

inline void validate_expr(const complex_exprt &value)
{
  validate_operands(value, 2, "Complex constructor must have two operands");
}

/// \brief Cast an exprt to a \ref complex_exprt
///
/// \a expr must be known to be \ref complex_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref complex_exprt
inline const complex_exprt &to_complex_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_complex);
  const complex_exprt &ret = static_cast<const complex_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_complex_expr(const exprt &)
inline complex_exprt &to_complex_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_complex);
  complex_exprt &ret = static_cast<complex_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Real part of the expression describing a complex number.
class complex_real_exprt : public unary_exprt
{
public:
  explicit complex_real_exprt(const exprt &op)
    : unary_exprt(ID_complex_real, op, to_complex_type(op.type()).subtype())
  {
  }
};

template <>
inline bool can_cast_expr<complex_real_exprt>(const exprt &base)
{
  return base.id() == ID_complex_real;
}

inline void validate_expr(const complex_real_exprt &expr)
{
  validate_operands(
    expr, 1, "real part retrieval operation must have one operand");
}

/// \brief Cast an exprt to a \ref complex_real_exprt
///
/// \a expr must be known to be a \ref complex_real_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref complex_real_exprt
inline const complex_real_exprt &to_complex_real_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_complex_real);
  const complex_real_exprt &ret = static_cast<const complex_real_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_complex_real_expr(const exprt &)
inline complex_real_exprt &to_complex_real_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_complex_real);
  complex_real_exprt &ret = static_cast<complex_real_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Imaginary part of the expression describing a complex number.
class complex_imag_exprt : public unary_exprt
{
public:
  explicit complex_imag_exprt(const exprt &op)
    : unary_exprt(ID_complex_imag, op, to_complex_type(op.type()).subtype())
  {
  }
};

template <>
inline bool can_cast_expr<complex_imag_exprt>(const exprt &base)
{
  return base.id() == ID_complex_imag;
}

inline void validate_expr(const complex_imag_exprt &expr)
{
  validate_operands(
    expr, 1, "imaginary part retrieval operation must have one operand");
}

/// \brief Cast an exprt to a \ref complex_imag_exprt
///
/// \a expr must be known to be a \ref complex_imag_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref complex_imag_exprt
inline const complex_imag_exprt &to_complex_imag_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_complex_imag);
  const complex_imag_exprt &ret = static_cast<const complex_imag_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_complex_imag_expr(const exprt &)
inline complex_imag_exprt &to_complex_imag_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_complex_imag);
  complex_imag_exprt &ret = static_cast<complex_imag_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Semantic type conversion
class typecast_exprt:public unary_exprt
{
public:
  typecast_exprt(exprt op, typet _type)
    : unary_exprt(ID_typecast, std::move(op), std::move(_type))
  {
  }

  // returns a typecast if the type doesn't already match
  static exprt conditional_cast(const exprt &expr, const typet &type)
  {
    if(expr.type() == type)
      return expr;
    else
      return typecast_exprt(expr, type);
  }
};

template <>
inline bool can_cast_expr<typecast_exprt>(const exprt &base)
{
  return base.id() == ID_typecast;
}

inline void validate_expr(const typecast_exprt &value)
{
  validate_operands(value, 1, "Typecast must have one operand");
}

/// \brief Cast an exprt to a \ref typecast_exprt
///
/// \a expr must be known to be \ref typecast_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref typecast_exprt
inline const typecast_exprt &to_typecast_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_typecast);
  const typecast_exprt &ret = static_cast<const typecast_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_typecast_expr(const exprt &)
inline typecast_exprt &to_typecast_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_typecast);
  typecast_exprt &ret = static_cast<typecast_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Boolean AND
class and_exprt:public multi_ary_exprt
{
public:
  and_exprt(exprt op0, exprt op1)
    : multi_ary_exprt(std::move(op0), ID_and, std::move(op1), bool_typet())
  {
  }

  and_exprt(exprt op0, exprt op1, exprt op2)
    : multi_ary_exprt(
        ID_and,
        {std::move(op0), std::move(op1), std::move(op2)},
        bool_typet())
  {
  }

  and_exprt(exprt op0, exprt op1, exprt op2, exprt op3)
    : multi_ary_exprt(
        ID_and,
        {std::move(op0), std::move(op1), std::move(op2), std::move(op3)},
        bool_typet())
  {
  }

  explicit and_exprt(exprt::operandst _operands)
    : multi_ary_exprt(ID_and, std::move(_operands), bool_typet())
  {
  }
};

/// 1) generates a conjunction for two or more operands
/// 2) for one operand, returns the operand
/// 3) returns true otherwise

exprt conjunction(const exprt::operandst &);

template <>
inline bool can_cast_expr<and_exprt>(const exprt &base)
{
  return base.id() == ID_and;
}

/// \brief Cast an exprt to a \ref and_exprt
///
/// \a expr must be known to be \ref and_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref and_exprt
inline const and_exprt &to_and_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_and);
  return static_cast<const and_exprt &>(expr);
}

/// \copydoc to_and_expr(const exprt &)
inline and_exprt &to_and_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_and);
  return static_cast<and_exprt &>(expr);
}


/// \brief Boolean implication
class implies_exprt:public binary_exprt
{
public:
  implies_exprt(exprt op0, exprt op1)
    : binary_exprt(std::move(op0), ID_implies, std::move(op1), bool_typet())
  {
  }
};

template <>
inline bool can_cast_expr<implies_exprt>(const exprt &base)
{
  return base.id() == ID_implies;
}

inline void validate_expr(const implies_exprt &value)
{
  validate_operands(value, 2, "Implies must have two operands");
}

/// \brief Cast an exprt to a \ref implies_exprt
///
/// \a expr must be known to be \ref implies_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref implies_exprt
inline const implies_exprt &to_implies_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_implies);
  const implies_exprt &ret = static_cast<const implies_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_implies_expr(const exprt &)
inline implies_exprt &to_implies_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_implies);
  implies_exprt &ret = static_cast<implies_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Boolean OR
class or_exprt:public multi_ary_exprt
{
public:
  or_exprt(exprt op0, exprt op1)
    : multi_ary_exprt(std::move(op0), ID_or, std::move(op1), bool_typet())
  {
  }

  or_exprt(exprt op0, exprt op1, exprt op2)
    : multi_ary_exprt(
        ID_or,
        {std::move(op0), std::move(op1), std::move(op2)},
        bool_typet())
  {
  }

  or_exprt(exprt op0, exprt op1, exprt op2, exprt op3)
    : multi_ary_exprt(
        ID_or,
        {std::move(op0), std::move(op1), std::move(op2), std::move(op3)},
        bool_typet())
  {
  }

  explicit or_exprt(exprt::operandst _operands)
    : multi_ary_exprt(ID_or, std::move(_operands), bool_typet())
  {
  }
};

/// 1) generates a disjunction for two or more operands
/// 2) for one operand, returns the operand
/// 3) returns false otherwise

exprt disjunction(const exprt::operandst &);

template <>
inline bool can_cast_expr<or_exprt>(const exprt &base)
{
  return base.id() == ID_or;
}

/// \brief Cast an exprt to a \ref or_exprt
///
/// \a expr must be known to be \ref or_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref or_exprt
inline const or_exprt &to_or_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_or);
  return static_cast<const or_exprt &>(expr);
}

/// \copydoc to_or_expr(const exprt &)
inline or_exprt &to_or_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_or);
  return static_cast<or_exprt &>(expr);
}


/// \brief Boolean XOR
class xor_exprt:public multi_ary_exprt
{
public:
  xor_exprt(exprt _op0, exprt _op1)
    : multi_ary_exprt(std::move(_op0), ID_xor, std::move(_op1), bool_typet())
  {
  }
};

template <>
inline bool can_cast_expr<xor_exprt>(const exprt &base)
{
  return base.id() == ID_xor;
}

/// \brief Cast an exprt to a \ref xor_exprt
///
/// \a expr must be known to be \ref xor_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref xor_exprt
inline const xor_exprt &to_xor_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_xor);
  return static_cast<const xor_exprt &>(expr);
}

/// \copydoc to_xor_expr(const exprt &)
inline xor_exprt &to_xor_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_xor);
  return static_cast<xor_exprt &>(expr);
}


/// \brief Boolean negation
class not_exprt:public unary_exprt
{
public:
  explicit not_exprt(exprt _op) : unary_exprt(ID_not, std::move(_op))
  {
    PRECONDITION(as_const(*this).op().type().id() == ID_bool);
  }
};

template <>
inline bool can_cast_expr<not_exprt>(const exprt &base)
{
  return base.id() == ID_not;
}

inline void validate_expr(const not_exprt &value)
{
  validate_operands(value, 1, "Not must have one operand");
}

/// \brief Cast an exprt to an \ref not_exprt
///
/// \a expr must be known to be \ref not_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref not_exprt
inline const not_exprt &to_not_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_not);
  const not_exprt &ret = static_cast<const not_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_not_expr(const exprt &)
inline not_exprt &to_not_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_not);
  not_exprt &ret = static_cast<not_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief The trinary if-then-else operator
class if_exprt : public ternary_exprt
{
public:
  if_exprt(exprt cond, const exprt &t, exprt f)
    : ternary_exprt(ID_if, std::move(cond), t, std::move(f), t.type())
  {
  }

  if_exprt(exprt cond, exprt t, exprt f, typet type)
    : ternary_exprt(
        ID_if,
        std::move(cond),
        std::move(t),
        std::move(f),
        std::move(type))
  {
  }

  exprt &cond()
  {
    return op0();
  }

  const exprt &cond() const
  {
    return op0();
  }

  exprt &true_case()
  {
    return op1();
  }

  const exprt &true_case() const
  {
    return op1();
  }

  exprt &false_case()
  {
    return op2();
  }

  const exprt &false_case() const
  {
    return op2();
  }

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    ternary_exprt::check(expr, vm);
  }

  static void validate(
    const exprt &expr,
    const namespacet &ns,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    ternary_exprt::validate(expr, ns, vm);
  }
};

template <>
inline bool can_cast_expr<if_exprt>(const exprt &base)
{
  return base.id() == ID_if;
}

inline void validate_expr(const if_exprt &value)
{
  validate_operands(value, 3, "If-then-else must have three operands");
}

/// \brief Cast an exprt to an \ref if_exprt
///
/// \a expr must be known to be \ref if_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref if_exprt
inline const if_exprt &to_if_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_if);
  const if_exprt &ret = static_cast<const if_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_if_expr(const exprt &)
inline if_exprt &to_if_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_if);
  if_exprt &ret = static_cast<if_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Operator to update elements in structs and arrays
/// \remark This expression will eventually be replaced by separate
///   array and struct update operators.
class with_exprt : public expr_protectedt
{
public:
  with_exprt(const exprt &_old, exprt _where, exprt _new_value)
    : expr_protectedt(
        ID_with,
        _old.type(),
        {_old, std::move(_where), std::move(_new_value)})
  {
  }

  exprt &old()
  {
    return op0();
  }

  const exprt &old() const
  {
    return op0();
  }

  exprt &where()
  {
    return op1();
  }

  const exprt &where() const
  {
    return op1();
  }

  exprt &new_value()
  {
    return op2();
  }

  const exprt &new_value() const
  {
    return op2();
  }
};

template <>
inline bool can_cast_expr<with_exprt>(const exprt &base)
{
  return base.id() == ID_with;
}

inline void validate_expr(const with_exprt &value)
{
  validate_operands(
    value, 3, "array/structure update must have at least 3 operands", true);
  DATA_INVARIANT(
    value.operands().size() % 2 == 1,
    "array/structure update must have an odd number of operands");
}

/// \brief Cast an exprt to a \ref with_exprt
///
/// \a expr must be known to be \ref with_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref with_exprt
inline const with_exprt &to_with_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_with);
  const with_exprt &ret = static_cast<const with_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_with_expr(const exprt &)
inline with_exprt &to_with_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_with);
  with_exprt &ret = static_cast<with_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class index_designatort : public expr_protectedt
{
public:
  explicit index_designatort(exprt _index)
    : expr_protectedt(ID_index_designator, typet(), {std::move(_index)})
  {
  }

  const exprt &index() const
  {
    return op0();
  }

  exprt &index()
  {
    return op0();
  }
};

template <>
inline bool can_cast_expr<index_designatort>(const exprt &base)
{
  return base.id() == ID_index_designator;
}

inline void validate_expr(const index_designatort &value)
{
  validate_operands(value, 1, "Index designator must have one operand");
}

/// \brief Cast an exprt to an \ref index_designatort
///
/// \a expr must be known to be \ref index_designatort.
///
/// \param expr: Source expression
/// \return Object of type \ref index_designatort
inline const index_designatort &to_index_designator(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_index_designator);
  const index_designatort &ret = static_cast<const index_designatort &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_index_designator(const exprt &)
inline index_designatort &to_index_designator(exprt &expr)
{
  PRECONDITION(expr.id()==ID_index_designator);
  index_designatort &ret = static_cast<index_designatort &>(expr);
  validate_expr(ret);
  return ret;
}

class member_designatort : public expr_protectedt
{
public:
  explicit member_designatort(const irep_idt &_component_name)
    : expr_protectedt(ID_member_designator, typet())
  {
    set(ID_component_name, _component_name);
  }

  irep_idt get_component_name() const
  {
    return get(ID_component_name);
  }
};

template <>
inline bool can_cast_expr<member_designatort>(const exprt &base)
{
  return base.id() == ID_member_designator;
}

inline void validate_expr(const member_designatort &value)
{
  validate_operands(value, 0, "Member designator must not have operands");
}

/// \brief Cast an exprt to an \ref member_designatort
///
/// \a expr must be known to be \ref member_designatort.
///
/// \param expr: Source expression
/// \return Object of type \ref member_designatort
inline const member_designatort &to_member_designator(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_member_designator);
  const member_designatort &ret = static_cast<const member_designatort &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_member_designator(const exprt &)
inline member_designatort &to_member_designator(exprt &expr)
{
  PRECONDITION(expr.id()==ID_member_designator);
  member_designatort &ret = static_cast<member_designatort &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Operator to update elements in structs and arrays
class update_exprt : public ternary_exprt
{
public:
  update_exprt(const exprt &_old, exprt _designator, exprt _new_value)
    : ternary_exprt(
        ID_update,
        _old,
        std::move(_designator),
        std::move(_new_value),
        _old.type())
  {
  }

  exprt &old()
  {
    return op0();
  }

  const exprt &old() const
  {
    return op0();
  }

  // the designator operands are either
  // 1) member_designator or
  // 2) index_designator
  // as defined above
  exprt::operandst &designator()
  {
    return op1().operands();
  }

  const exprt::operandst &designator() const
  {
    return op1().operands();
  }

  exprt &new_value()
  {
    return op2();
  }

  const exprt &new_value() const
  {
    return op2();
  }

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    ternary_exprt::check(expr, vm);
  }

  static void validate(
    const exprt &expr,
    const namespacet &ns,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    ternary_exprt::validate(expr, ns, vm);
  }
};

template <>
inline bool can_cast_expr<update_exprt>(const exprt &base)
{
  return base.id() == ID_update;
}

inline void validate_expr(const update_exprt &value)
{
  validate_operands(
    value, 3, "Array/structure update must have three operands");
}

/// \brief Cast an exprt to an \ref update_exprt
///
/// \a expr must be known to be \ref update_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref update_exprt
inline const update_exprt &to_update_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_update);
  const update_exprt &ret = static_cast<const update_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_update_expr(const exprt &)
inline update_exprt &to_update_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_update);
  update_exprt &ret = static_cast<update_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


#if 0
/// \brief Update of one element of an array
class array_update_exprt:public expr_protectedt
{
public:
  array_update_exprt(
    const exprt &_array,
    const exprt &_index,
    const exprt &_new_value):
    exprt(ID_array_update, _array.type())
  {
    add_to_operands(_array, _index, _new_value);
  }

  array_update_exprt():expr_protectedt(ID_array_update)
  {
    operands().resize(3);
  }

  exprt &array()
  {
    return op0();
  }

  const exprt &array() const
  {
    return op0();
  }

  exprt &index()
  {
    return op1();
  }

  const exprt &index() const
  {
    return op1();
  }

  exprt &new_value()
  {
    return op2();
  }

  const exprt &new_value() const
  {
    return op2();
  }
};

template<> inline bool can_cast_expr<array_update_exprt>(const exprt &base)
{
  return base.id()==ID_array_update;
}

inline void validate_expr(const array_update_exprt &value)
{
  validate_operands(value, 3, "Array update must have three operands");
}

/// \brief Cast an exprt to an \ref array_update_exprt
///
/// \a expr must be known to be \ref array_update_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref array_update_exprt
inline const array_update_exprt &to_array_update_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_array_update);
  const array_update_exprt &ret = static_cast<const array_update_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_array_update_expr(const exprt &)
inline array_update_exprt &to_array_update_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_array_update);
  array_update_exprt &ret = static_cast<array_update_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

#endif


/// \brief Extract member of struct or union
class member_exprt:public unary_exprt
{
public:
  member_exprt(exprt op, const irep_idt &component_name, typet _type)
    : unary_exprt(ID_member, std::move(op), std::move(_type))
  {
    set_component_name(component_name);
  }

  member_exprt(exprt op, const struct_typet::componentt &c)
    : unary_exprt(ID_member, std::move(op), c.type())
  {
    set_component_name(c.get_name());
  }

  irep_idt get_component_name() const
  {
    return get(ID_component_name);
  }

  void set_component_name(const irep_idt &component_name)
  {
    set(ID_component_name, component_name);
  }

  std::size_t get_component_number() const
  {
    return get_size_t(ID_component_number);
  }

  // will go away, use compound()
  const exprt &struct_op() const
  {
    return op0();
  }

  // will go away, use compound()
  exprt &struct_op()
  {
    return op0();
  }

  const exprt &compound() const
  {
    return op0();
  }

  exprt &compound()
  {
    return op0();
  }

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm,
      expr.operands().size() == 1,
      "member expression must have one operand");
  }

  static void validate(
    const exprt &expr,
    const namespacet &ns,
    const validation_modet vm = validation_modet::INVARIANT);
};

template <>
inline bool can_cast_expr<member_exprt>(const exprt &base)
{
  return base.id() == ID_member;
}

inline void validate_expr(const member_exprt &value)
{
  validate_operands(value, 1, "Extract member must have one operand");
}

/// \brief Cast an exprt to a \ref member_exprt
///
/// \a expr must be known to be \ref member_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref member_exprt
inline const member_exprt &to_member_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_member);
  const member_exprt &ret = static_cast<const member_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_member_expr(const exprt &)
inline member_exprt &to_member_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_member);
  member_exprt &ret = static_cast<member_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief An expression denoting a type
class type_exprt : public nullary_exprt
{
public:
  explicit type_exprt(typet type) : nullary_exprt(ID_type, std::move(type))
  {
  }
};

template <>
inline bool can_cast_expr<type_exprt>(const exprt &base)
{
  return base.id() == ID_type;
}

/// \brief Cast an exprt to an \ref type_exprt
///
/// \a expr must be known to be \ref type_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref type_exprt
inline const type_exprt &to_type_expr(const exprt &expr)
{
  PRECONDITION(can_cast_expr<type_exprt>(expr));
  const type_exprt &ret = static_cast<const type_exprt &>(expr);
  return ret;
}

/// \copydoc to_type_expr(const exprt &)
inline type_exprt &to_type_expr(exprt &expr)
{
  PRECONDITION(can_cast_expr<type_exprt>(expr));
  type_exprt &ret = static_cast<type_exprt &>(expr);
  return ret;
}

/// \brief A constant literal expression
class constant_exprt : public nullary_exprt
{
public:
  constant_exprt(const irep_idt &_value, typet _type)
    : nullary_exprt(ID_constant, std::move(_type))
  {
    set_value(_value);
  }

  const irep_idt &get_value() const
  {
    return get(ID_value);
  }

  void set_value(const irep_idt &value)
  {
    set(ID_value, value);
  }

  bool value_is_zero_string() const;

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT);

  static void validate(
    const exprt &expr,
    const namespacet &,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    check(expr, vm);
  }
};

template <>
inline bool can_cast_expr<constant_exprt>(const exprt &base)
{
  return base.id() == ID_constant;
}

inline void validate_expr(const constant_exprt &value)
{
  validate_operands(value, 0, "Constants must not have operands");
}

/// \brief Cast an exprt to a \ref constant_exprt
///
/// \a expr must be known to be \ref constant_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref constant_exprt
inline const constant_exprt &to_constant_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_constant);
  return static_cast<const constant_exprt &>(expr);
}

/// \copydoc to_constant_expr(const exprt &)
inline constant_exprt &to_constant_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_constant);
  return static_cast<constant_exprt &>(expr);
}


/// \brief The Boolean constant true
class true_exprt:public constant_exprt
{
public:
  true_exprt() : constant_exprt(ID_true, bool_typet())
  {
  }
};

/// \brief The Boolean constant false
class false_exprt:public constant_exprt
{
public:
  false_exprt() : constant_exprt(ID_false, bool_typet())
  {
  }
};

/// \brief The NIL expression
class nil_exprt : public nullary_exprt
{
public:
  nil_exprt()
    : nullary_exprt(static_cast<const nullary_exprt &>(get_nil_irep()))
  {
  }
};

template <>
inline bool can_cast_expr<nil_exprt>(const exprt &base)
{
  return base.id() == ID_nil;
}

/// \brief An expression denoting infinity
class infinity_exprt : public nullary_exprt
{
public:
  explicit infinity_exprt(typet _type)
    : nullary_exprt(ID_infinity, std::move(_type))
  {
  }
};

/// \brief A base class for variable bindings (quantifiers, let, lambda)
class binding_exprt : public binary_exprt
{
public:
  using variablest = std::vector<symbol_exprt>;

  /// construct the binding expression
  binding_exprt(
    irep_idt _id,
    const variablest &_variables,
    exprt _where,
    typet _type)
    : binary_exprt(
        multi_ary_exprt(
          ID_tuple,
          (const operandst &)_variables,
          typet(ID_tuple)),
        _id,
        std::move(_where),
        std::move(_type))
  {
  }

  variablest &variables()
  {
    return (variablest &)to_multi_ary_expr(op0()).operands();
  }

  const variablest &variables() const
  {
    return (variablest &)to_multi_ary_expr(op0()).operands();
  }

  exprt &where()
  {
    return op1();
  }

  const exprt &where() const
  {
    return op1();
  }

  /// substitute free occurrences of the variables in where()
  /// by the given values
  exprt instantiate(const exprt::operandst &) const;

  /// substitute free occurrences of the variables in where()
  /// by a set of different symbols
  exprt instantiate(const variablest &) const;
};

inline void validate_expr(const binding_exprt &binding_expr)
{
  validate_operands(
    binding_expr, 2, "Binding expressions must have two operands");
}

/// \brief Cast an exprt to a \ref binding_exprt
///
/// \a expr must be known to be \ref binding_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref binding_exprt
inline const binding_exprt &to_binding_expr(const exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_forall || expr.id() == ID_exists ||
    expr.id() == ID_lambda || expr.id() == ID_array_comprehension);
  const binding_exprt &ret = static_cast<const binding_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Cast an exprt to a \ref binding_exprt
///
/// \a expr must be known to be \ref binding_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref binding_exprt
inline binding_exprt &to_binding_expr(exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_forall || expr.id() == ID_exists ||
    expr.id() == ID_lambda || expr.id() == ID_array_comprehension);
  binding_exprt &ret = static_cast<binding_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief A let expression
class let_exprt : public binary_exprt
{
public:
  let_exprt(
    binding_exprt::variablest variables,
    operandst values,
    const exprt &where)
    : binary_exprt(
        binding_exprt(
          ID_let_binding,
          std::move(variables),
          where,
          where.type()),
        ID_let,
        multi_ary_exprt(irep_idt(), std::move(values), typet(ID_tuple)),
        where.type())
  {
    PRECONDITION(this->variables().size() == this->values().size());
  }

  /// convenience constructor for the case of a single binding
  let_exprt(symbol_exprt symbol, exprt value, const exprt &where)
    : let_exprt(
        binding_exprt::variablest{std::move(symbol)},
        operandst{std::move(value)},
        where)
  {
  }

  binding_exprt &binding()
  {
    return static_cast<binding_exprt &>(op0());
  }

  const binding_exprt &binding() const
  {
    return static_cast<const binding_exprt &>(op0());
  }

  /// convenience accessor for the symbol of a single binding
  symbol_exprt &symbol()
  {
    auto &variables = binding().variables();
    PRECONDITION(variables.size() == 1);
    return variables.front();
  }

  /// convenience accessor for the symbol of a single binding
  const symbol_exprt &symbol() const
  {
    const auto &variables = binding().variables();
    PRECONDITION(variables.size() == 1);
    return variables.front();
  }

  /// convenience accessor for the value of a single binding
  exprt &value()
  {
    auto &values = this->values();
    PRECONDITION(values.size() == 1);
    return values.front();
  }

  /// convenience accessor for the value of a single binding
  const exprt &value() const
  {
    const auto &values = this->values();
    PRECONDITION(values.size() == 1);
    return values.front();
  }

  operandst &values()
  {
    return static_cast<multi_ary_exprt &>(op1()).operands();
  }

  const operandst &values() const
  {
    return static_cast<const multi_ary_exprt &>(op1()).operands();
  }

  /// convenience accessor for binding().variables()
  binding_exprt::variablest &variables()
  {
    return binding().variables();
  }

  /// convenience accessor for binding().variables()
  const binding_exprt::variablest &variables() const
  {
    return binding().variables();
  }

  /// convenience accessor for binding().where()
  exprt &where()
  {
    return binding().where();
  }

  /// convenience accessor for binding().where()
  const exprt &where() const
  {
    return binding().where();
  }

  static void validate(const exprt &, validation_modet);
};

template <>
inline bool can_cast_expr<let_exprt>(const exprt &base)
{
  return base.id() == ID_let;
}

inline void validate_expr(const let_exprt &let_expr)
{
  validate_operands(let_expr, 2, "Let must have two operands");
}

/// \brief Cast an exprt to a \ref let_exprt
///
/// \a expr must be known to be \ref let_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref let_exprt
inline const let_exprt &to_let_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_let);
  const let_exprt &ret = static_cast<const let_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_let_expr(const exprt &)
inline let_exprt &to_let_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_let);
  let_exprt &ret = static_cast<let_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// this is a parametric version of an if-expression: it returns
/// the value of the first case (using the ordering of the operands)
/// whose condition evaluates to true.
class cond_exprt : public multi_ary_exprt
{
public:
  cond_exprt(operandst _operands, typet _type)
    : multi_ary_exprt(ID_cond, std::move(_operands), std::move(_type))
  {
  }

  /// adds a case to a cond expression
  /// \param condition: the condition for the case
  /// \param value: the value for the case
  void add_case(const exprt &condition, const exprt &value)
  {
    PRECONDITION(condition.type().id() == ID_bool);
    operands().reserve(operands().size() + 2);
    operands().push_back(condition);
    operands().push_back(value);
  }
};

template <>
inline bool can_cast_expr<cond_exprt>(const exprt &base)
{
  return base.id() == ID_cond;
}

inline void validate_expr(const cond_exprt &value)
{
  DATA_INVARIANT(
    value.operands().size() % 2 == 0, "cond must have even number of operands");
}

/// \brief Cast an exprt to a \ref cond_exprt
///
/// \a expr must be known to be \ref cond_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref cond_exprt
inline const cond_exprt &to_cond_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_cond);
  const cond_exprt &ret = static_cast<const cond_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_cond_expr(const exprt &)
inline cond_exprt &to_cond_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_cond);
  cond_exprt &ret = static_cast<cond_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Expression to define a mapping from an argument (index) to elements.
/// This enables constructing an array via an anonymous function.
/// Not all kinds of array comprehension can be expressed, only those of the
/// form `[f(x) | x in {0, 1, ... array_size-1}]`.
/// The LHS and RHS are the argument (`x`) and body (`f(x)`) of the anonymous
/// function, respectively. The range is given by the type of the expression,
/// which has to be an \ref array_typet (which includes a value for
/// `array_size`).
class array_comprehension_exprt : public binding_exprt
{
public:
  explicit array_comprehension_exprt(
    symbol_exprt arg,
    exprt body,
    array_typet _type)
    : binding_exprt(
        ID_array_comprehension,
        {std::move(arg)},
        std::move(body),
        std::move(_type))
  {
  }

  const array_typet &type() const
  {
    return static_cast<const array_typet &>(binary_exprt::type());
  }

  array_typet &type()
  {
    return static_cast<array_typet &>(binary_exprt::type());
  }

  const symbol_exprt &arg() const
  {
    auto &variables = this->variables();
    PRECONDITION(variables.size() == 1);
    return variables[0];
  }

  symbol_exprt &arg()
  {
    auto &variables = this->variables();
    PRECONDITION(variables.size() == 1);
    return variables[0];
  }

  const exprt &body() const
  {
    return where();
  }

  exprt &body()
  {
    return where();
  }
};

template <>
inline bool can_cast_expr<array_comprehension_exprt>(const exprt &base)
{
  return base.id() == ID_array_comprehension;
}

inline void validate_expr(const array_comprehension_exprt &value)
{
  validate_operands(value, 2, "'Array comprehension' must have two operands");
}

/// \brief Cast an exprt to a \ref array_comprehension_exprt
///
/// \a expr must be known to be \ref array_comprehension_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref array_comprehension_exprt
inline const array_comprehension_exprt &
to_array_comprehension_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_array_comprehension);
  const array_comprehension_exprt &ret =
    static_cast<const array_comprehension_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_array_comprehension_expr(const exprt &)
inline array_comprehension_exprt &to_array_comprehension_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_array_comprehension);
  array_comprehension_exprt &ret =
    static_cast<array_comprehension_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

inline void validate_expr(const class class_method_descriptor_exprt &value);

/// An expression describing a method on a class
class class_method_descriptor_exprt : public nullary_exprt
{
public:
  /// \param _type: The type of the method which this expression refers to.
  /// \param class_id: Unique identifier in the symbol table, of the compile
  ///   time type of the class which this expression is applied to. For example
  ///   this could be - `java::java.lang.Object`.
  /// \param base_method_name: The name of the method to which this expression
  ///   is applied as would be seen in the source code. For example this could
  ///   be - `toString`.
  /// \param mangled_method_name: The method name after mangling it by
  ///   combining it with the descriptor. The mangled name is distinguished from
  ///   other overloads of the method with different counts of or types of
  ///   parameters. It is not distinguished between different implementations
  ///   within a class hierarchy. For example if the overall expression refers
  ///   to the `java.lang.Object.toString` method, then the mangled_method_name
  ///   would be `toString:()Ljava/lang/String;`
  explicit class_method_descriptor_exprt(
    typet _type,
    irep_idt mangled_method_name,
    irep_idt class_id,
    irep_idt base_method_name)
    : nullary_exprt(ID_virtual_function, std::move(_type))
  {
    irep_idt id = id2string(class_id) + "." + id2string(mangled_method_name);
    set(ID_component_name, std::move(mangled_method_name));
    set(ID_C_class, std::move(class_id));
    set(ID_C_base_name, std::move(base_method_name));
    set(ID_identifier, std::move(id));
    validate_expr(*this);
  }

  /// The method name after mangling it by combining it with the descriptor.
  /// The mangled name is distinguished from other overloads of the method with
  /// different counts of or types of parameters. It is not distinguished
  /// between different implementations within a class hierarchy. For example if
  /// the overall expression refers to the `java.lang.Object.toString` method,
  /// then the mangled_method_name would be `toString:()Ljava/lang/String;`
  const irep_idt &mangled_method_name() const
  {
    return get(ID_component_name);
  }

  /// Unique identifier in the symbol table, of the compile time type of the
  /// class which this expression is applied to. For example this could be -
  /// `java::java.lang.Object`.
  const irep_idt &class_id() const
  {
    return get(ID_C_class);
  }

  /// The name of the method to which this expression is applied as would be
  /// seen in the source code. For example this could be - `toString`.
  const irep_idt &base_method_name() const
  {
    return get(ID_C_base_name);
  }

  /// A unique identifier of the combination of class and method overload to
  /// which this expression refers. For example this could be -
  /// `java::java.lang.Object.toString:()Ljava/lang/String;`.
  const irep_idt &get_identifier() const
  {
    return get(ID_identifier);
  }
};

inline void validate_expr(const class class_method_descriptor_exprt &value)
{
  validate_operands(value, 0, "class method descriptor must not have operands");
  DATA_INVARIANT(
    !value.mangled_method_name().empty(),
    "class method descriptor must have a mangled method name.");
  DATA_INVARIANT(
    !value.class_id().empty(), "class method descriptor must have a class id.");
  DATA_INVARIANT(
    !value.base_method_name().empty(),
    "class method descriptor must have a base method name.");
  DATA_INVARIANT(
    value.get_identifier() == id2string(value.class_id()) + "." +
                                id2string(value.mangled_method_name()),
    "class method descriptor must have an identifier in the expected format.");
}

/// \brief Cast an exprt to a \ref class_method_descriptor_exprt
///
/// \a expr must be known to be \ref class_method_descriptor_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref class_method_descriptor_exprt
inline const class_method_descriptor_exprt &
to_class_method_descriptor_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_virtual_function);
  const class_method_descriptor_exprt &ret =
    static_cast<const class_method_descriptor_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

template <>
inline bool can_cast_expr<class_method_descriptor_exprt>(const exprt &base)
{
  return base.id() == ID_virtual_function;
}

#endif // CPROVER_UTIL_STD_EXPR_H
