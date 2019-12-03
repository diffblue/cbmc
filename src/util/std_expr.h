/*******************************************************************\

Module: API to expression classes

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_STD_EXPR_H
#define CPROVER_UTIL_STD_EXPR_H

/// \file util/std_expr.h
/// API to expression classes

#include "as_const.h"
#include "expr_cast.h"
#include "invariant.h"
#include "narrow.h"
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

  void move_to_operands(exprt &) = delete;
  void move_to_operands(exprt &, exprt &) = delete;
  void move_to_operands(exprt &, exprt &, exprt &) = delete;

  void copy_to_operands(const exprt &expr) = delete;
  void copy_to_operands(const exprt &, const exprt &) = delete;
  void copy_to_operands(const exprt &, const exprt &, const exprt &) = delete;
};

/// An expression with three operands
class ternary_exprt : public expr_protectedt
{
public:
  // constructors
  DEPRECATED(
    SINCE(2018, 9, 21, "use ternary_exprt(id, op0, op1, op2, type) instead"))
  explicit ternary_exprt(const irep_idt &_id) : expr_protectedt(_id, type())
  {
    operands().resize(3);
  }

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
};

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

  DEPRECATED(SINCE(2018, 12, 2, "use unary_exprt(id, op, type) instead"))
  unary_exprt(const irep_idt &_id, const typet &_type)
    : expr_protectedt(_id, _type)
  {
    operands().resize(1);
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

/// \brief The byte swap expression
class bswap_exprt: public unary_exprt
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
    set(ID_bits_per_byte, narrow_cast<long long>(bits_per_byte));
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

/// \brief A base class for expressions that are predicates,
///   i.e., Boolean-typed.
class predicate_exprt : public expr_protectedt
{
public:
  DEPRECATED(SINCE(2018, 12, 2, "use predicate_exprt(id) instead"))
  predicate_exprt() : expr_protectedt(irep_idt(), bool_typet())
  {
  }

  explicit predicate_exprt(const irep_idt &_id)
    : expr_protectedt(_id, bool_typet())
  {
  }

  DEPRECATED(SINCE(2018, 12, 2, "use unary_predicate_exprt(id, op) instead"))
  predicate_exprt(const irep_idt &_id, const exprt &_op)
    : expr_protectedt(_id, bool_typet())
  {
    add_to_operands(_op);
  }

  DEPRECATED(
    SINCE(2018, 12, 2, "use binary_predicate_exprt(op1, id, op2) instead"))
  predicate_exprt(const irep_idt &_id, const exprt &_op0, const exprt &_op1)
    : expr_protectedt(_id, bool_typet())
  {
    add_to_operands(_op0, _op1);
  }
};

/// \brief A base class for expressions that are predicates,
///   i.e., Boolean-typed, and that take exactly one argument.
class unary_predicate_exprt:public unary_exprt
{
public:
  DEPRECATED(SINCE(2018, 12, 2, "use unary_predicate_exprt(id, op) instead"))
  unary_predicate_exprt():unary_exprt(irep_idt(), bool_typet())
  {
  }

  DEPRECATED(SINCE(2018, 12, 2, "use unary_predicate_exprt(id, op) instead"))
  explicit unary_predicate_exprt(const irep_idt &_id):
    unary_exprt(_id, bool_typet())
  {
  }

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
  DEPRECATED(SINCE(2018, 12, 2, "use sign_exprt(op) instead"))
  sign_exprt()
  {
  }

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
  DEPRECATED(SINCE(2018, 9, 21, "use binary_exprt(lhs, id, rhs) instead"))
  explicit binary_exprt(const irep_idt &_id) : expr_protectedt(_id, typet())
  {
    operands().resize(2);
  }

  DEPRECATED(SINCE(2018, 12, 2, "use binary_exprt(lhs, id, rhs, type) instead"))
  binary_exprt(const irep_idt &_id, const typet &_type)
    : expr_protectedt(_id, _type)
  {
    operands().resize(2);
  }

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
  DEPRECATED(
    SINCE(2018, 12, 2, "use binary_predicate_exprt(lhs, id, rhs) instead"))
  binary_predicate_exprt():binary_exprt(irep_idt(), bool_typet())
  {
  }

  DEPRECATED(
    SINCE(2018, 12, 2, "use binary_predicate_exprt(lhs, id, rhs) instead"))
  explicit binary_predicate_exprt(const irep_idt &_id):
    binary_exprt(_id, bool_typet())
  {
  }

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
  DEPRECATED(
    SINCE(2018, 12, 2, "use binary_relation_exprt(lhs, id, rhs) instead"))
  binary_relation_exprt()
  {
  }

  DEPRECATED(
    SINCE(2018, 12, 2, "use binary_relation_exprt(lhs, id, rhs) instead"))
  explicit binary_relation_exprt(const irep_idt &id):
    binary_predicate_exprt(id)
  {
  }

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
  DEPRECATED(SINCE(2018, 9, 21, "use multi_ary_exprt(id, op, type) instead"))
  explicit multi_ary_exprt(const irep_idt &_id) : expr_protectedt(_id, typet())
  {
  }

  DEPRECATED(SINCE(2018, 12, 7, "use multi_ary_exprt(id, op, type) instead"))
  multi_ary_exprt(const irep_idt &_id, const typet &_type)
    : expr_protectedt(_id, _type)
  {
  }

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
  DEPRECATED(SINCE(2019, 1, 12, "use plus_exprt(lhs, rhs, type) instead"))
  plus_exprt(const typet &type) : multi_ary_exprt(ID_plus, type)
  {
  }

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


/// \brief Modulo
class mod_exprt:public binary_exprt
{
public:
  mod_exprt(exprt _lhs, exprt _rhs)
    : binary_exprt(std::move(_lhs), ID_mod, std::move(_rhs))
  {
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


/// \brief Remainder of division
class rem_exprt:public binary_exprt
{
public:
  rem_exprt(exprt _lhs, exprt _rhs)
    : binary_exprt(std::move(_lhs), ID_rem, std::move(_rhs))
  {
  }
};

template <>
inline bool can_cast_expr<rem_exprt>(const exprt &base)
{
  return base.id() == ID_rem;
}

inline void validate_expr(const rem_exprt &value)
{
  validate_operands(value, 2, "Remainder must have two operands");
}

/// \brief Cast an exprt to a \ref rem_exprt
///
/// \a expr must be known to be \ref rem_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref rem_exprt
inline const rem_exprt &to_rem_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_rem);
  const rem_exprt &ret = static_cast<const rem_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_rem_expr(const exprt &)
inline rem_exprt &to_rem_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_rem);
  rem_exprt &ret = static_cast<rem_exprt &>(expr);
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
  index_exprt(const exprt &_array, exprt _index)
    : binary_exprt(_array, ID_index, std::move(_index), _array.type().subtype())
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
  DEPRECATED(SINCE(2019, 1, 12, "use array_exprt(operands, type) instead"))
  explicit array_exprt(const array_typet &_type)
    : multi_ary_exprt(ID_array, _type)
  {
  }

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
  DEPRECATED(SINCE(2019, 1, 12, "use array_list_exprt(operands, type) instead"))
  explicit array_list_exprt(const array_typet &_type)
    : multi_ary_exprt(ID_array_list, _type)
  {
  }

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
  DEPRECATED(SINCE(2019, 1, 12, "use vector_exprt(operands, type) instead"))
  explicit vector_exprt(const vector_typet &_type)
    : multi_ary_exprt(ID_vector, _type)
  {
  }

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
    set(ID_component_number, narrow_cast<long long>(component_number));
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


/// \brief Struct constructor from list of elements
class struct_exprt : public multi_ary_exprt
{
public:
  DEPRECATED(SINCE(2019, 1, 12, "use struct_exprt(operands, type) instead"))
  explicit struct_exprt(const typet &_type) : multi_ary_exprt(ID_struct, _type)
  {
  }

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

class namespacet;

/// \brief Split an expression into a base object and a (byte) offset
class object_descriptor_exprt:public binary_exprt
{
public:
  object_descriptor_exprt()
    : binary_exprt(
        exprt(ID_unknown),
        ID_object_descriptor,
        exprt(ID_unknown),
        typet())
  {
  }

  explicit object_descriptor_exprt(exprt _object)
    : binary_exprt(
        std::move(_object),
        ID_object_descriptor,
        exprt(ID_unknown),
        typet())
  {
  }

  /// Given an expression \p expr, attempt to find the underlying object it
  /// represents by skipping over type casts and removing balanced
  /// dereference/address_of operations; that object will then be available
  /// as root_object().
  void build(const exprt &expr, const namespacet &ns);

  exprt &object()
  {
    return op0();
  }

  const exprt &object() const
  {
    return op0();
  }

  const exprt &root_object() const;

  exprt &offset()
  {
    return op1();
  }

  const exprt &offset() const
  {
    return op1();
  }
};

template <>
inline bool can_cast_expr<object_descriptor_exprt>(const exprt &base)
{
  return base.id() == ID_object_descriptor;
}

inline void validate_expr(const object_descriptor_exprt &value)
{
  validate_operands(value, 2, "Object descriptor must have two operands");
}

/// \brief Cast an exprt to an \ref object_descriptor_exprt
///
/// \a expr must be known to be \ref object_descriptor_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref object_descriptor_exprt
inline const object_descriptor_exprt &to_object_descriptor_expr(
  const exprt &expr)
{
  PRECONDITION(expr.id()==ID_object_descriptor);
  const object_descriptor_exprt &ret =
    static_cast<const object_descriptor_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_object_descriptor_expr(const exprt &)
inline object_descriptor_exprt &to_object_descriptor_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_object_descriptor);
  object_descriptor_exprt &ret = static_cast<object_descriptor_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// Representation of heap-allocated objects
class dynamic_object_exprt:public binary_exprt
{
public:
  DEPRECATED(SINCE(2019, 2, 11, "use dynamic_object_exprt(type) instead"))
  dynamic_object_exprt()
    : binary_exprt(exprt(ID_unknown), ID_dynamic_object, exprt(ID_unknown))
  {
  }

  explicit dynamic_object_exprt(typet type)
    : binary_exprt(
        exprt(ID_unknown),
        ID_dynamic_object,
        exprt(ID_unknown),
        std::move(type))
  {
  }

  void set_instance(unsigned int instance);

  unsigned int get_instance() const;

  exprt &valid()
  {
    return op1();
  }

  const exprt &valid() const
  {
    return op1();
  }
};

template <>
inline bool can_cast_expr<dynamic_object_exprt>(const exprt &base)
{
  return base.id() == ID_dynamic_object;
}

inline void validate_expr(const dynamic_object_exprt &value)
{
  validate_operands(value, 2, "Dynamic object must have two operands");
}

/// \brief Cast an exprt to a \ref dynamic_object_exprt
///
/// \a expr must be known to be \ref dynamic_object_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref dynamic_object_exprt
inline const dynamic_object_exprt &to_dynamic_object_expr(
  const exprt &expr)
{
  PRECONDITION(expr.id()==ID_dynamic_object);
  const dynamic_object_exprt &ret =
    static_cast<const dynamic_object_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_dynamic_object_expr(const exprt &)
inline dynamic_object_exprt &to_dynamic_object_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_dynamic_object);
  dynamic_object_exprt &ret = static_cast<dynamic_object_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// Evaluates to true if the operand is a pointer to a dynamic object.
class is_dynamic_object_exprt : public unary_predicate_exprt
{
public:
  is_dynamic_object_exprt() : unary_predicate_exprt(ID_is_dynamic_object)
  {
  }

  explicit is_dynamic_object_exprt(const exprt &op)
    : unary_predicate_exprt(ID_is_dynamic_object, op)
  {
  }
};

inline const is_dynamic_object_exprt &
to_is_dynamic_object_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_is_dynamic_object);
  DATA_INVARIANT(
    expr.operands().size() == 1, "is_dynamic_object must have one operand");
  return static_cast<const is_dynamic_object_exprt &>(expr);
}

/// \copydoc to_is_dynamic_object_expr(const exprt &)
/// \ingroup gr_std_expr
inline is_dynamic_object_exprt &to_is_dynamic_object_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_is_dynamic_object);
  DATA_INVARIANT(
    expr.operands().size() == 1, "is_dynamic_object must have one operand");
  return static_cast<is_dynamic_object_exprt &>(expr);
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


/// \brief Semantic type conversion from/to floating-point formats
class floatbv_typecast_exprt:public binary_exprt
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
  PRECONDITION(expr.id()==ID_floatbv_typecast);
  const floatbv_typecast_exprt &ret =
    static_cast<const floatbv_typecast_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_floatbv_typecast_expr(const exprt &)
inline floatbv_typecast_exprt &to_floatbv_typecast_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_floatbv_typecast);
  floatbv_typecast_exprt &ret = static_cast<floatbv_typecast_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Boolean AND
class and_exprt:public multi_ary_exprt
{
public:
  DEPRECATED(SINCE(2019, 1, 12, "use and_exprt(op, op) instead"))
  and_exprt():multi_ary_exprt(ID_and, bool_typet())
  {
  }

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
  DEPRECATED(SINCE(2019, 1, 12, "use or_exprt(op, op) instead"))
  or_exprt():multi_ary_exprt(ID_or, bool_typet())
  {
  }

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
  DEPRECATED(SINCE(2019, 1, 12, "use xor_exprt(op, op) instead"))
  xor_exprt():multi_ary_exprt(ID_bitxor, bool_typet())
  {
  }

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

/// \copydoc to_bitxor_expr(const exprt &)
inline xor_exprt &to_xor_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_xor);
  return static_cast<xor_exprt &>(expr);
}


/// \brief Bit-wise negation of bit-vectors
class bitnot_exprt:public unary_exprt
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
  PRECONDITION(expr.id()==ID_bitnot);
  const bitnot_exprt &ret = static_cast<const bitnot_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_bitnot_expr(const exprt &)
inline bitnot_exprt &to_bitnot_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_bitnot);
  bitnot_exprt &ret = static_cast<bitnot_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Bit-wise OR
class bitor_exprt:public multi_ary_exprt
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
  PRECONDITION(expr.id()==ID_bitor);
  return static_cast<const bitor_exprt &>(expr);
}

/// \copydoc to_bitor_expr(const exprt &)
inline bitor_exprt &to_bitor_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_bitor);
  return static_cast<bitor_exprt &>(expr);
}


/// \brief Bit-wise XOR
class bitxor_exprt:public multi_ary_exprt
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
  PRECONDITION(expr.id()==ID_bitxor);
  return static_cast<const bitxor_exprt &>(expr);
}

/// \copydoc to_bitxor_expr(const exprt &)
inline bitxor_exprt &to_bitxor_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_bitxor);
  return static_cast<bitxor_exprt &>(expr);
}


/// \brief Bit-wise AND
class bitand_exprt:public multi_ary_exprt
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
  PRECONDITION(expr.id()==ID_bitand);
  return static_cast<const bitand_exprt &>(expr);
}

/// \copydoc to_bitand_expr(const exprt &)
inline bitand_exprt &to_bitand_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_bitand);
  return static_cast<bitand_exprt &>(expr);
}


/// \brief A base class for shift operators
class shift_exprt:public binary_exprt
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
  return base.id() == ID_shl || base.id() == ID_ashr || base.id() == ID_lshr;
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
class shl_exprt:public shift_exprt
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
class ashr_exprt:public shift_exprt
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

/// \brief Logical right shift
class lshr_exprt:public shift_exprt
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

/// \brief Extracts a single bit of a bit-vector operand
class extractbit_exprt:public binary_predicate_exprt
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
  PRECONDITION(expr.id()==ID_extractbit);
  const extractbit_exprt &ret = static_cast<const extractbit_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_extractbit_expr(const exprt &)
inline extractbit_exprt &to_extractbit_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_extractbit);
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
  PRECONDITION(expr.id()==ID_extractbits);
  const extractbits_exprt &ret = static_cast<const extractbits_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_extractbits_expr(const exprt &)
inline extractbits_exprt &to_extractbits_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_extractbits);
  extractbits_exprt &ret = static_cast<extractbits_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Operator to return the address of an object
class address_of_exprt:public unary_exprt
{
public:
  explicit address_of_exprt(const exprt &op);

  address_of_exprt(exprt op, pointer_typet _type)
    : unary_exprt(ID_address_of, std::move(op), std::move(_type))
  {
  }

  exprt &object()
  {
    return op0();
  }

  const exprt &object() const
  {
    return op0();
  }
};

template <>
inline bool can_cast_expr<address_of_exprt>(const exprt &base)
{
  return base.id() == ID_address_of;
}

inline void validate_expr(const address_of_exprt &value)
{
  validate_operands(value, 1, "Address of must have one operand");
}

/// \brief Cast an exprt to an \ref address_of_exprt
///
/// \a expr must be known to be \ref address_of_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref address_of_exprt
inline const address_of_exprt &to_address_of_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_address_of);
  const address_of_exprt &ret = static_cast<const address_of_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_address_of_expr(const exprt &)
inline address_of_exprt &to_address_of_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_address_of);
  address_of_exprt &ret = static_cast<address_of_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Boolean negation
class not_exprt:public unary_exprt
{
public:
  explicit not_exprt(exprt _op) : unary_exprt(ID_not, std::move(_op))
  {
    PRECONDITION(as_const(*this).op().type().id() == ID_bool);
  }

  DEPRECATED(SINCE(2019, 1, 12, "use not_exprt(op) instead"))
  not_exprt():unary_exprt(ID_not, bool_typet())
  {
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


/// \brief Operator to dereference a pointer
class dereference_exprt:public unary_exprt
{
public:
  explicit dereference_exprt(const exprt &op):
    unary_exprt(ID_dereference, op, op.type().subtype())
  {
    PRECONDITION(op.type().id()==ID_pointer);
  }

  dereference_exprt(exprt op, typet type)
    : unary_exprt(ID_dereference, std::move(op), std::move(type))
  {
  }

  exprt &pointer()
  {
    return op0();
  }

  const exprt &pointer() const
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
      "dereference expression must have one operand");
  }

  static void validate(
    const exprt &expr,
    const namespacet &ns,
    const validation_modet vm = validation_modet::INVARIANT);
};

template <>
inline bool can_cast_expr<dereference_exprt>(const exprt &base)
{
  return base.id() == ID_dereference;
}

inline void validate_expr(const dereference_exprt &value)
{
  validate_operands(value, 1, "Dereference must have one operand");
}

/// \brief Cast an exprt to a \ref dereference_exprt
///
/// \a expr must be known to be \ref dereference_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref dereference_exprt
inline const dereference_exprt &to_dereference_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_dereference);
  const dereference_exprt &ret = static_cast<const dereference_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_dereference_expr(const exprt &)
inline dereference_exprt &to_dereference_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_dereference);
  dereference_exprt &ret = static_cast<dereference_exprt &>(expr);
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


/// \brief Evaluates to true if the operand is NaN
class isnan_exprt:public unary_predicate_exprt
{
public:
  explicit isnan_exprt(exprt op)
    : unary_predicate_exprt(ID_isnan, std::move(op))
  {
  }

  DEPRECATED(SINCE(2018, 12, 2, "use isnan_exprt(op) instead"))
  isnan_exprt():unary_predicate_exprt(ID_isnan)
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
  PRECONDITION(expr.id()==ID_isnan);
  const isnan_exprt &ret = static_cast<const isnan_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_isnan_expr(const exprt &)
inline isnan_exprt &to_isnan_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_isnan);
  isnan_exprt &ret = static_cast<isnan_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Evaluates to true if the operand is infinite
class isinf_exprt:public unary_predicate_exprt
{
public:
  explicit isinf_exprt(exprt op)
    : unary_predicate_exprt(ID_isinf, std::move(op))
  {
  }

  DEPRECATED(SINCE(2018, 12, 2, "use isinf_exprt(op) instead"))
  isinf_exprt():unary_predicate_exprt(ID_isinf)
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
  PRECONDITION(expr.id()==ID_isinf);
  const isinf_exprt &ret = static_cast<const isinf_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_isinf_expr(const exprt &)
inline isinf_exprt &to_isinf_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_isinf);
  isinf_exprt &ret = static_cast<isinf_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Evaluates to true if the operand is finite
class isfinite_exprt:public unary_predicate_exprt
{
public:
  explicit isfinite_exprt(exprt op)
    : unary_predicate_exprt(ID_isfinite, std::move(op))
  {
  }

  DEPRECATED(SINCE(2018, 12, 2, "use isfinite_exprt(op) instead"))
  isfinite_exprt():unary_predicate_exprt(ID_isfinite)
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
  PRECONDITION(expr.id()==ID_isfinite);
  const isfinite_exprt &ret = static_cast<const isfinite_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_isfinite_expr(const exprt &)
inline isfinite_exprt &to_isfinite_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_isfinite);
  isfinite_exprt &ret = static_cast<isfinite_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief Evaluates to true if the operand is a normal number
class isnormal_exprt:public unary_predicate_exprt
{
public:
  explicit isnormal_exprt(exprt op)
    : unary_predicate_exprt(ID_isnormal, std::move(op))
  {
  }

  DEPRECATED(SINCE(2018, 12, 2, "use isnormal_exprt(op) instead"))
  isnormal_exprt():unary_predicate_exprt(ID_isnormal)
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
  PRECONDITION(expr.id()==ID_isnormal);
  const isnormal_exprt &ret = static_cast<const isnormal_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_isnormal_expr(const exprt &)
inline isnormal_exprt &to_isnormal_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_isnormal);
  isnormal_exprt &ret = static_cast<isnormal_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief IEEE-floating-point equality
class ieee_float_equal_exprt:public binary_relation_exprt
{
public:
  DEPRECATED(SINCE(2018, 12, 2, "use ieee_float_equal_exprt(lhs, rhs) instead"))
  ieee_float_equal_exprt():binary_relation_exprt(ID_ieee_float_equal)
  {
  }

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
  PRECONDITION(expr.id()==ID_ieee_float_equal);
  const ieee_float_equal_exprt &ret =
    static_cast<const ieee_float_equal_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_ieee_float_equal_expr(const exprt &)
inline ieee_float_equal_exprt &to_ieee_float_equal_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_ieee_float_equal);
  ieee_float_equal_exprt &ret = static_cast<ieee_float_equal_exprt &>(expr);
  validate_expr(ret);
  return ret;
}


/// \brief IEEE floating-point disequality
class ieee_float_notequal_exprt:public binary_relation_exprt
{
public:
  DEPRECATED(
    SINCE(2018, 12, 2, "use ieee_float_notequal_exprt(lhs, rhs) instead"))
  ieee_float_notequal_exprt():
    binary_relation_exprt(ID_ieee_float_notequal)
  {
  }

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
inline const ieee_float_notequal_exprt &to_ieee_float_notequal_expr(
  const exprt &expr)
{
  PRECONDITION(expr.id()==ID_ieee_float_notequal);
  const ieee_float_notequal_exprt &ret =
    static_cast<const ieee_float_notequal_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_ieee_float_notequal_expr(const exprt &)
inline ieee_float_notequal_exprt &to_ieee_float_notequal_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_ieee_float_notequal);
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
class constant_exprt : public expr_protectedt
{
public:
  constant_exprt(const irep_idt &_value, typet _type)
    : expr_protectedt(ID_constant, std::move(_type))
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
};

template <>
inline bool can_cast_expr<constant_exprt>(const exprt &base)
{
  return base.id() == ID_constant;
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

/// \brief The null pointer constant
class null_pointer_exprt:public constant_exprt
{
public:
  explicit null_pointer_exprt(pointer_typet type)
    : constant_exprt(ID_NULL, std::move(type))
  {
  }
};

/// \brief Bit-vector replication
class replication_exprt : public binary_exprt
{
public:
  replication_exprt(const constant_exprt &_times, const exprt &_src)
    : binary_exprt(_times, ID_replication, _src)
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
  PRECONDITION(expr.id()==ID_concatenation);
  return static_cast<const concatenation_exprt &>(expr);
}

/// \copydoc to_concatenation_expr(const exprt &)
inline concatenation_exprt &to_concatenation_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_concatenation);
  return static_cast<concatenation_exprt &>(expr);
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
};

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

/// \brief The popcount (counting the number of bits set to 1) expression
class popcount_exprt: public unary_exprt
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

/// this is a parametric version of an if-expression: it returns
/// the value of the first case (using the ordering of the operands)
/// whose condition evaluates to true.
class cond_exprt : public multi_ary_exprt
{
public:
  DEPRECATED(SINCE(2019, 1, 12, "use cond_exprt(operands, type) instead"))
  explicit cond_exprt(const typet &_type) : multi_ary_exprt(ID_cond, _type)
  {
  }

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

/// \copydoc to_popcount_expr(const exprt &)
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
class array_comprehension_exprt : public binary_exprt
{
public:
  explicit array_comprehension_exprt(
    symbol_exprt arg,
    exprt body,
    array_typet _type)
    : binary_exprt(
        std::move(arg),
        ID_array_comprehension,
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
    return static_cast<const symbol_exprt &>(op0());
  }

  symbol_exprt &arg()
  {
    return static_cast<symbol_exprt &>(op0());
  }

  const exprt &body() const
  {
    return op1();
  }

  exprt &body()
  {
    return op1();
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
