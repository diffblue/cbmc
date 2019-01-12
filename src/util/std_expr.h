/*******************************************************************\

Module: API to expression classes

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_STD_EXPR_H
#define CPROVER_UTIL_STD_EXPR_H

/// \file util/std_expr.h
/// API to expression classes

#include "base_type.h"
#include "expr_cast.h"
#include "invariant.h"
#include "mathematical_types.h"
#include "std_types.h"

/// An expression without operands
class nullary_exprt : public exprt
{
public:
  // constructors
  DEPRECATED("use nullary_exprt(id, type) instead")
  explicit nullary_exprt(const irep_idt &_id) : exprt(_id)
  {
  }

  nullary_exprt(const irep_idt &_id, const typet &_type) : exprt(_id, _type)
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
class ternary_exprt : public exprt
{
public:
  // constructors
  DEPRECATED("use ternary_exprt(id, op0, op1, op2, type) instead")
  explicit ternary_exprt(const irep_idt &_id) : exprt(_id)
  {
    operands().resize(3);
  }

  DEPRECATED("use ternary_exprt(id, op0, op1, op2, type) instead")
  explicit ternary_exprt(const irep_idt &_id, const typet &_type)
    : exprt(_id, _type)
  {
    operands().resize(3);
  }

  ternary_exprt(
    const irep_idt &_id,
    const exprt &_op0,
    const exprt &_op1,
    const exprt &_op2,
    const typet &_type)
    : exprt(_id, _type)
  {
    add_to_operands(_op0, _op1, _op2);
  }

  const exprt &op3() const = delete;
  exprt &op3() = delete;
};

/// Transition system, consisting of state invariant, initial state predicate,
/// and transition predicate.
class transt : public ternary_exprt
{
public:
  transt() : ternary_exprt(ID_trans)
  {
  }

  exprt &invar() { return op0(); }
  exprt &init()  { return op1(); }
  exprt &trans() { return op2(); }

  const exprt &invar() const { return op0(); }
  const exprt &init()  const { return op1(); }
  const exprt &trans() const { return op2(); }
};

/// Cast an exprt to a \ref transt
/// \a expr must be known to be \ref transt.
/// \param expr: Source expression
/// \return Object of type \ref transt
inline const transt &to_trans_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_trans);
  DATA_INVARIANT(
    expr.operands().size()==3,
    "Transition systems must have three operands");
  return static_cast<const transt &>(expr);
}

/// \copydoc to_trans_expr(const exprt &)
inline transt &to_trans_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_trans);
  DATA_INVARIANT(
    expr.operands().size()==3,
    "Transition systems must have three operands");
  return static_cast<transt &>(expr);
}

template<> inline bool can_cast_expr<transt>(const exprt &base)
{
  return base.id()==ID_trans;
}
inline void validate_expr(const transt &value)
{
  validate_operands(value, 3, "Transition systems must have three operands");
}


/// Expression to hold a symbol (variable)
class symbol_exprt : public nullary_exprt
{
public:
  DEPRECATED("use symbol_exprt(identifier, type) instead")
  symbol_exprt() : nullary_exprt(ID_symbol)
  {
  }

  /// \param identifier: Name of symbol
  DEPRECATED("use symbol_exprt(identifier, type) instead")
  explicit symbol_exprt(const irep_idt &identifier) : nullary_exprt(ID_symbol)
  {
    set_identifier(identifier);
  }

  /// \param type: Type of symbol
  explicit symbol_exprt(const typet &type) : nullary_exprt(ID_symbol, type)
  {
  }

  /// \param identifier: Name of symbol
  /// \param type: Type of symbol
  symbol_exprt(const irep_idt &identifier, const typet &type)
    : nullary_exprt(ID_symbol, type)
  {
    set_identifier(identifier);
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
  DEPRECATED("use decorated_symbol_exprt(identifier, type) instead")
  decorated_symbol_exprt()
  {
  }

  /// \param identifier: Name of symbol
  DEPRECATED("use decorated_symbol_exprt(identifier, type) instead")
  explicit decorated_symbol_exprt(const irep_idt &identifier):
    symbol_exprt(identifier)
  {
  }

  /// \param type: Type of symbol
  DEPRECATED("use decorated_symbol_exprt(identifier, type) instead")
  explicit decorated_symbol_exprt(const typet &type):
    symbol_exprt(type)
  {
  }

  /// \param identifier: Name of symbol
  /// \param type: Type of symbol
  decorated_symbol_exprt(
    const irep_idt &identifier,
    const typet &type):symbol_exprt(identifier, type)
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

/// \brief Cast an exprt to a \ref symbol_exprt
///
/// \a expr must be known to be \ref symbol_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref symbol_exprt
inline const symbol_exprt &to_symbol_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_symbol);
  DATA_INVARIANT(!expr.has_operands(), "Symbols must not have operands");
  return static_cast<const symbol_exprt &>(expr);
}

/// \copydoc to_symbol_expr(const exprt &)
inline symbol_exprt &to_symbol_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_symbol);
  DATA_INVARIANT(!expr.has_operands(), "Symbols must not have operands");
  return static_cast<symbol_exprt &>(expr);
}

template<> inline bool can_cast_expr<symbol_exprt>(const exprt &base)
{
  return base.id()==ID_symbol;
}
inline void validate_expr(const symbol_exprt &value)
{
  validate_operands(value, 0, "Symbols must not have operands");
}


/// \brief Expression to hold a nondeterministic choice
class nondet_symbol_exprt : public nullary_exprt
{
public:
  /// \param identifier: Name of symbol
  /// \param type: Type of symbol
  nondet_symbol_exprt(const irep_idt &identifier, const typet &type)
    : nullary_exprt(ID_nondet_symbol, type)
  {
    set_identifier(identifier);
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

/// \brief Cast an exprt to a \ref nondet_symbol_exprt
///
/// \a expr must be known to be \ref nondet_symbol_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref nondet_symbol_exprt
inline const nondet_symbol_exprt &to_nondet_symbol_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_nondet_symbol);
  DATA_INVARIANT(!expr.has_operands(), "Symbols must not have operands");
  return static_cast<const nondet_symbol_exprt &>(expr);
}

/// \copydoc to_nondet_symbol_expr(const exprt &)
inline nondet_symbol_exprt &to_nondet_symbol_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_symbol);
  DATA_INVARIANT(!expr.has_operands(), "Symbols must not have operands");
  return static_cast<nondet_symbol_exprt &>(expr);
}

template<> inline bool can_cast_expr<nondet_symbol_exprt>(const exprt &base)
{
  return base.id()==ID_nondet_symbol;
}
inline void validate_expr(const nondet_symbol_exprt &value)
{
  validate_operands(value, 0, "Symbols must not have operands");
}


/// \brief Generic base class for unary expressions
class unary_exprt:public exprt
{
public:
  DEPRECATED("use unary_exprt(id, op) instead")
  unary_exprt()
  {
    operands().resize(1);
  }

  DEPRECATED("use unary_exprt(id, op) instead")
  explicit unary_exprt(const irep_idt &_id):exprt(_id)
  {
    operands().resize(1);
  }

  unary_exprt(
    const irep_idt &_id,
    const exprt &_op):
    exprt(_id, _op.type())
  {
    add_to_operands(_op);
  }

  DEPRECATED("use unary_exprt(id, op, type) instead")
  unary_exprt(
    const irep_idt &_id,
    const typet &_type):exprt(_id, _type)
  {
    operands().resize(1);
  }

  unary_exprt(
    const irep_idt &_id,
    const exprt &_op,
    const typet &_type):
    exprt(_id, _type)
  {
    add_to_operands(_op);
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

/// \brief Cast an exprt to a \ref unary_exprt
///
/// \a expr must be known to be \ref unary_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref unary_exprt
inline const unary_exprt &to_unary_expr(const exprt &expr)
{
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Unary expressions must have one operand");
  return static_cast<const unary_exprt &>(expr);
}

/// \copydoc to_unary_expr(const exprt &)
inline unary_exprt &to_unary_expr(exprt &expr)
{
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Unary expressions must have one operand");
  return static_cast<unary_exprt &>(expr);
}

template<> inline bool can_cast_expr<unary_exprt>(const exprt &base)
{
  return base.operands().size()==1;
}


/// \brief Absolute value
class abs_exprt:public unary_exprt
{
public:
  DEPRECATED("use abs_exprt(op) instead")
  abs_exprt()
  {
  }

  explicit abs_exprt(const exprt &_op):
    unary_exprt(ID_abs, _op, _op.type())
  {
  }
};

/// \brief Cast an exprt to a \ref abs_exprt
///
/// \a expr must be known to be \ref abs_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref abs_exprt
inline const abs_exprt &to_abs_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_abs);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Absolute value must have one operand");
  return static_cast<const abs_exprt &>(expr);
}

/// \copydoc to_abs_expr(const exprt &)
inline abs_exprt &to_abs_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_abs);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Absolute value must have one operand");
  return static_cast<abs_exprt &>(expr);
}

template<> inline bool can_cast_expr<abs_exprt>(const exprt &base)
{
  return base.id()==ID_abs;
}
inline void validate_expr(const abs_exprt &value)
{
  validate_operands(value, 1, "Absolute value must have one operand");
}


/// \brief The unary minus expression
class unary_minus_exprt:public unary_exprt
{
public:
  DEPRECATED("use unary_minus_exprt(op) instead")
  unary_minus_exprt():unary_exprt(ID_unary_minus)
  {
  }

  unary_minus_exprt(
    const exprt &_op,
    const typet &_type):
    unary_exprt(ID_unary_minus, _op, _type)
  {
  }

  explicit unary_minus_exprt(const exprt &_op):
    unary_exprt(ID_unary_minus, _op, _op.type())
  {
  }
};

/// \brief Cast an exprt to a \ref unary_minus_exprt
///
/// \a expr must be known to be \ref unary_minus_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref unary_minus_exprt
inline const unary_minus_exprt &to_unary_minus_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_unary_minus);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Unary minus must have one operand");
  return static_cast<const unary_minus_exprt &>(expr);
}

/// \copydoc to_unary_minus_expr(const exprt &)
inline unary_minus_exprt &to_unary_minus_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_unary_minus);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Unary minus must have one operand");
  return static_cast<unary_minus_exprt &>(expr);
}

template<> inline bool can_cast_expr<unary_minus_exprt>(const exprt &base)
{
  return base.id()==ID_unary_minus;
}
inline void validate_expr(const unary_minus_exprt &value)
{
  validate_operands(value, 1, "Unary minus must have one operand");
}

/// \brief The unary plus expression
class unary_plus_exprt : public unary_exprt
{
public:
  explicit unary_plus_exprt(const exprt &op)
    : unary_exprt(ID_unary_plus, op, op.type())
  {
  }
};

/// \brief Cast an exprt to a \ref unary_plus_exprt
///
/// \a expr must be known to be \ref unary_plus_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref unary_plus_exprt
inline const unary_plus_exprt &to_unary_plus_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_unary_plus);
  DATA_INVARIANT(
    expr.operands().size() == 1, "unary plus must have one operand");
  return static_cast<const unary_plus_exprt &>(expr);
}

/// \copydoc to_unary_minus_expr(const exprt &)
inline unary_plus_exprt &to_unary_plus_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_unary_plus);
  DATA_INVARIANT(
    expr.operands().size() == 1, "unary plus must have one operand");
  return static_cast<unary_plus_exprt &>(expr);
}

template <>
inline bool can_cast_expr<unary_plus_exprt>(const exprt &base)
{
  return base.id() == ID_unary_plus;
}
inline void validate_expr(const unary_plus_exprt &value)
{
  validate_operands(value, 1, "unary plus must have one operand");
}

/// \brief The byte swap expression
class bswap_exprt: public unary_exprt
{
public:
  bswap_exprt(const exprt &_op, std::size_t bits_per_byte, const typet &_type)
    : unary_exprt(ID_bswap, _op, _type)
  {
    set_bits_per_byte(bits_per_byte);
  }

  bswap_exprt(const exprt &_op, std::size_t bits_per_byte)
    : unary_exprt(ID_bswap, _op, _op.type())
  {
    set_bits_per_byte(bits_per_byte);
  }

  std::size_t get_bits_per_byte() const
  {
    return get_size_t(ID_bits_per_byte);
  }

  void set_bits_per_byte(std::size_t bits_per_byte)
  {
    set(ID_bits_per_byte, bits_per_byte);
  }
};

/// \brief Cast an exprt to a \ref bswap_exprt
///
/// \a expr must be known to be \ref bswap_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref bswap_exprt
inline const bswap_exprt &to_bswap_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_bswap);
  DATA_INVARIANT(expr.operands().size() == 1, "bswap must have one operand");
  DATA_INVARIANT(
    expr.op0().type() == expr.type(), "bswap type must match operand type");
  return static_cast<const bswap_exprt &>(expr);
}

/// \copydoc to_bswap_expr(const exprt &)
inline bswap_exprt &to_bswap_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_bswap);
  DATA_INVARIANT(expr.operands().size() == 1, "bswap must have one operand");
  DATA_INVARIANT(
    expr.op0().type() == expr.type(), "bswap type must match operand type");
  return static_cast<bswap_exprt &>(expr);
}

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

/// \brief A base class for expressions that are predicates,
///   i.e., Boolean-typed.
class predicate_exprt:public exprt
{
public:
  DEPRECATED("use predicate_exprt(id) instead")
  predicate_exprt():exprt(irep_idt(), bool_typet())
  {
  }

  explicit predicate_exprt(const irep_idt &_id):
    exprt(_id, bool_typet())
  {
  }

  DEPRECATED("use unary_predicate_exprt(id, op) instead")
  predicate_exprt(
    const irep_idt &_id,
    const exprt &_op):exprt(_id, bool_typet())
  {
    add_to_operands(_op);
  }

  DEPRECATED("use binary_predicate_exprt(op1, id, op2) instead")
  predicate_exprt(
    const irep_idt &_id,
    const exprt &_op0,
    const exprt &_op1):exprt(_id, bool_typet())
  {
    add_to_operands(_op0, _op1);
  }
};

/// \brief A base class for expressions that are predicates,
///   i.e., Boolean-typed, and that take exactly one argument.
class unary_predicate_exprt:public unary_exprt
{
public:
  DEPRECATED("use unary_predicate_exprt(id, op) instead")
  unary_predicate_exprt():unary_exprt(irep_idt(), bool_typet())
  {
  }

  DEPRECATED("use unary_predicate_exprt(id, op) instead")
  explicit unary_predicate_exprt(const irep_idt &_id):
    unary_exprt(_id, bool_typet())
  {
  }

  unary_predicate_exprt(
    const irep_idt &_id,
    const exprt &_op):unary_exprt(_id, _op, bool_typet())
  {
  }

};

/// \brief Sign of an expression
/// Predicate is true if \a _op is negative, false otherwise.
class sign_exprt:public unary_predicate_exprt
{
public:
  DEPRECATED("use sign_exprt(op) instead")
  sign_exprt()
  {
  }

  explicit sign_exprt(const exprt &_op):
    unary_predicate_exprt(ID_sign, _op)
  {
  }
};

/// \brief Cast an exprt to a \ref sign_exprt
///
/// \a expr must be known to be a \ref sign_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref sign_exprt
inline const sign_exprt &to_sign_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_sign);
  DATA_INVARIANT(
    expr.operands().size() == 1, "sign expression must have one operand");
  return static_cast<const sign_exprt &>(expr);
}

/// \copydoc to_sign_expr(const exprt &)
inline sign_exprt &to_sign_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_sign);
  DATA_INVARIANT(
    expr.operands().size() == 1, "sign expression must have one operand");
  return static_cast<sign_exprt &>(expr);
}

template <>
inline bool can_cast_expr<sign_exprt>(const exprt &base)
{
  return base.id() == ID_sign;
}
inline void validate_expr(const sign_exprt &expr)
{
  validate_operands(expr, 1, "sign expression must have one operand");
}

/// \brief A base class for binary expressions
class binary_exprt:public exprt
{
public:
  DEPRECATED("use binary_exprt(lhs, id, rhs) instead")
  binary_exprt()
  {
    operands().resize(2);
  }

  DEPRECATED("use binary_exprt(lhs, id, rhs) instead")
  explicit binary_exprt(const irep_idt &_id):exprt(_id)
  {
    operands().resize(2);
  }

  DEPRECATED("use binary_exprt(lhs, id, rhs, type) instead")
  binary_exprt(
    const irep_idt &_id,
    const typet &_type):exprt(_id, _type)
  {
    operands().resize(2);
  }

  binary_exprt(
    const exprt &_lhs,
    const irep_idt &_id,
    const exprt &_rhs):
    exprt(_id, _lhs.type())
  {
    add_to_operands(_lhs, _rhs);
  }

  binary_exprt(
    const exprt &_lhs,
    const irep_idt &_id,
    const exprt &_rhs,
    const typet &_type):
    exprt(_id, _type)
  {
    add_to_operands(_lhs, _rhs);
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

  const exprt &op2() const = delete;
  exprt &op2() = delete;
  const exprt &op3() const = delete;
  exprt &op3() = delete;
};

/// \brief Cast an exprt to a \ref binary_exprt
///
/// \a expr must be known to be \ref binary_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref binary_exprt
inline const binary_exprt &to_binary_expr(const exprt &expr)
{
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Binary expressions must have two operands");
  return static_cast<const binary_exprt &>(expr);
}

/// \copydoc to_binary_expr(const exprt &)
inline binary_exprt &to_binary_expr(exprt &expr)
{
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Binary expressions must have two operands");
  return static_cast<binary_exprt &>(expr);
}

template<> inline bool can_cast_expr<binary_exprt>(const exprt &base)
{
  return base.operands().size()==2;
}

/// \brief A base class for expressions that are predicates,
///   i.e., Boolean-typed, and that take exactly two arguments.
class binary_predicate_exprt:public binary_exprt
{
public:
  DEPRECATED("use binary_predicate_exprt(lhs, id, rhs) instead")
  binary_predicate_exprt():binary_exprt(irep_idt(), bool_typet())
  {
  }

  DEPRECATED("use binary_predicate_exprt(lhs, id, rhs) instead")
  explicit binary_predicate_exprt(const irep_idt &_id):
    binary_exprt(_id, bool_typet())
  {
  }

  binary_predicate_exprt(
    const exprt &_op0,
    const irep_idt &_id,
    const exprt &_op1):binary_exprt(_op0, _id, _op1, bool_typet())
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

/// \brief A base class for relations, i.e., binary predicates
class binary_relation_exprt:public binary_predicate_exprt
{
public:
  DEPRECATED("use binary_relation_exprt(lhs, id, rhs) instead")
  binary_relation_exprt()
  {
  }

  DEPRECATED("use binary_relation_exprt(lhs, id, rhs) instead")
  explicit binary_relation_exprt(const irep_idt &id):
    binary_predicate_exprt(id)
  {
  }

  binary_relation_exprt(
    const exprt &_lhs,
    const irep_idt &_id,
    const exprt &_rhs):
    binary_predicate_exprt(_lhs, _id, _rhs)
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

    // check types
    DATA_CHECK(
      vm,
      base_type_eq(expr.op0().type(), expr.op1().type(), ns),
      "lhs and rhs of binary relation expression should have same type");
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
};

/// \brief Cast an exprt to a \ref binary_relation_exprt
///
/// \a expr must be known to be \ref binary_relation_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref binary_relation_exprt
inline const binary_relation_exprt &to_binary_relation_expr(const exprt &expr)
{
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Binary relations must have two operands");
  return static_cast<const binary_relation_exprt &>(expr);
}

/// \copydoc to_binary_relation_expr(const exprt &)
inline binary_relation_exprt &to_binary_relation_expr(exprt &expr)
{
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Binary relations must have two operands");
  return static_cast<binary_relation_exprt &>(expr);
}

template<> inline bool can_cast_expr<binary_relation_exprt>(const exprt &base)
{
  return can_cast_expr<binary_exprt>(base);
}


/// \brief A base class for multi-ary expressions
/// Associativity is not specified.
class multi_ary_exprt:public exprt
{
public:
  DEPRECATED("use multi_ary_exprt(id, op, type) instead")
  multi_ary_exprt()
  {
  }

  DEPRECATED("use multi_ary_exprt(id, op, type) instead")
  explicit multi_ary_exprt(const irep_idt &_id):exprt(_id)
  {
  }

  DEPRECATED("use multi_ary_exprt(id, op, type) instead")
  multi_ary_exprt(
    const irep_idt &_id,
    const typet &_type):exprt(_id, _type)
  {
  }

  multi_ary_exprt(
    const irep_idt &_id,
    operandst &&_operands,
    const typet &_type)
    : exprt(_id, _type)
  {
    operands() = std::move(_operands);
  }

  multi_ary_exprt(
    const exprt &_lhs,
    const irep_idt &_id,
    const exprt &_rhs):
    exprt(_id, _lhs.type())
  {
    add_to_operands(_lhs, _rhs);
  }

  multi_ary_exprt(
    const exprt &_lhs,
    const irep_idt &_id,
    const exprt &_rhs,
    const typet &_type):
    exprt(_id, _type)
  {
    add_to_operands(_lhs, _rhs);
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
  DEPRECATED("use plus_exprt(lhs, rhs) instead")
  plus_exprt():multi_ary_exprt(ID_plus)
  {
  }

  plus_exprt(const typet &type) : multi_ary_exprt(ID_plus, type)
  {
  }

  plus_exprt(
    const exprt &_lhs,
    const exprt &_rhs):
    multi_ary_exprt(_lhs, ID_plus, _rhs)
  {
  }

  plus_exprt(
    const exprt &_lhs,
    const exprt &_rhs,
    const typet &_type):
    multi_ary_exprt(_lhs, ID_plus, _rhs, _type)
  {
  }
};

/// \brief Cast an exprt to a \ref plus_exprt
///
/// \a expr must be known to be \ref plus_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref plus_exprt
inline const plus_exprt &to_plus_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_plus);
  DATA_INVARIANT(
    expr.operands().size()>=2,
    "Plus must have two or more operands");
  return static_cast<const plus_exprt &>(expr);
}

/// \copydoc to_plus_expr(const exprt &)
inline plus_exprt &to_plus_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_plus);
  DATA_INVARIANT(
    expr.operands().size()>=2,
    "Plus must have two or more operands");
  return static_cast<plus_exprt &>(expr);
}

template<> inline bool can_cast_expr<plus_exprt>(const exprt &base)
{
  return base.id()==ID_plus;
}
inline void validate_expr(const plus_exprt &value)
{
  validate_operands(value, 2, "Plus must have two or more operands", true);
}


/// \brief Binary minus
class minus_exprt:public binary_exprt
{
public:
  DEPRECATED("use minus_exprt(lhs, rhs) instead")
  minus_exprt():binary_exprt(ID_minus)
  {
  }

  minus_exprt(
    const exprt &_lhs,
    const exprt &_rhs):
    binary_exprt(_lhs, ID_minus, _rhs)
  {
  }
};

/// \brief Cast an exprt to a \ref minus_exprt
///
/// \a expr must be known to be \ref minus_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref minus_exprt
inline const minus_exprt &to_minus_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_minus);
  DATA_INVARIANT(
    expr.operands().size()>=2,
    "Minus must have two or more operands");
  return static_cast<const minus_exprt &>(expr);
}

/// \copydoc to_minus_expr(const exprt &)
inline minus_exprt &to_minus_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_minus);
  DATA_INVARIANT(
    expr.operands().size()>=2,
    "Minus must have two or more operands");
  return static_cast<minus_exprt &>(expr);
}

template<> inline bool can_cast_expr<minus_exprt>(const exprt &base)
{
  return base.id()==ID_minus;
}
inline void validate_expr(const minus_exprt &value)
{
  validate_operands(value, 2, "Minus must have two or more operands", true);
}


/// \brief Binary multiplication
/// Associativity is not specified.
class mult_exprt:public multi_ary_exprt
{
public:
  DEPRECATED("use mult_exprt(lhs, rhs) instead")
  mult_exprt():multi_ary_exprt(ID_mult)
  {
  }

  mult_exprt(
    const exprt &_lhs,
    const exprt &_rhs):
    multi_ary_exprt(_lhs, ID_mult, _rhs)
  {
  }
};

/// \brief Cast an exprt to a \ref mult_exprt
///
/// \a expr must be known to be \ref mult_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref mult_exprt
inline const mult_exprt &to_mult_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_mult);
  DATA_INVARIANT(
    expr.operands().size()>=2,
    "Multiply must have two or more operands");
  return static_cast<const mult_exprt &>(expr);
}

/// \copydoc to_mult_expr(const exprt &)
inline mult_exprt &to_mult_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_mult);
  DATA_INVARIANT(
    expr.operands().size()>=2,
    "Multiply must have two or more operands");
  return static_cast<mult_exprt &>(expr);
}

template<> inline bool can_cast_expr<mult_exprt>(const exprt &base)
{
  return base.id()==ID_mult;
}
inline void validate_expr(const mult_exprt &value)
{
  validate_operands(value, 2, "Multiply must have two or more operands", true);
}


/// \brief Division
class div_exprt:public binary_exprt
{
public:
  DEPRECATED("use div_exprt(lhs, rhs) instead")
  div_exprt():binary_exprt(ID_div)
  {
  }

  div_exprt(
    const exprt &_lhs,
    const exprt &_rhs):
    binary_exprt(_lhs, ID_div, _rhs)
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

/// \brief Cast an exprt to a \ref div_exprt
///
/// \a expr must be known to be \ref div_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref div_exprt
inline const div_exprt &to_div_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_div);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Divide must have two operands");
  return static_cast<const div_exprt &>(expr);
}

/// \copydoc to_div_expr(const exprt &)
inline div_exprt &to_div_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_div);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Divide must have two operands");
  return static_cast<div_exprt &>(expr);
}

template<> inline bool can_cast_expr<div_exprt>(const exprt &base)
{
  return base.id()==ID_div;
}
inline void validate_expr(const div_exprt &value)
{
  validate_operands(value, 2, "Divide must have two operands");
}


/// \brief Modulo
class mod_exprt:public binary_exprt
{
public:
  DEPRECATED("use mod_exprt(lhs, rhs) instead")
  mod_exprt():binary_exprt(ID_mod)
  {
  }

  mod_exprt(
    const exprt &_lhs,
    const exprt &_rhs):
    binary_exprt(_lhs, ID_mod, _rhs)
  {
  }
};

/// \brief Cast an exprt to a \ref mod_exprt
///
/// \a expr must be known to be \ref mod_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref mod_exprt
inline const mod_exprt &to_mod_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_mod);
  DATA_INVARIANT(expr.operands().size()==2, "Modulo must have two operands");
  return static_cast<const mod_exprt &>(expr);
}

/// \copydoc to_mod_expr(const exprt &)
inline mod_exprt &to_mod_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_mod);
  DATA_INVARIANT(expr.operands().size()==2, "Modulo must have two operands");
  return static_cast<mod_exprt &>(expr);
}

template<> inline bool can_cast_expr<mod_exprt>(const exprt &base)
{
  return base.id()==ID_mod;
}
inline void validate_expr(const mod_exprt &value)
{
  validate_operands(value, 2, "Modulo must have two operands");
}


/// \brief Remainder of division
class rem_exprt:public binary_exprt
{
public:
  DEPRECATED("use rem_exprt(lhs, rhs) instead")
  rem_exprt():binary_exprt(ID_rem)
  {
  }

  rem_exprt(
    const exprt &_lhs,
    const exprt &_rhs):
    binary_exprt(_lhs, ID_rem, _rhs)
  {
  }
};

/// \brief Cast an exprt to a \ref rem_exprt
///
/// \a expr must be known to be \ref rem_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref rem_exprt
inline const rem_exprt &to_rem_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_rem);
  DATA_INVARIANT(expr.operands().size()==2, "Remainder must have two operands");
  return static_cast<const rem_exprt &>(expr);
}

/// \copydoc to_rem_expr(const exprt &)
inline rem_exprt &to_rem_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_rem);
  DATA_INVARIANT(expr.operands().size()==2, "Remainder must have two operands");
  return static_cast<rem_exprt &>(expr);
}

template<> inline bool can_cast_expr<rem_exprt>(const exprt &base)
{
  return base.id()==ID_rem;
}
inline void validate_expr(const rem_exprt &value)
{
  validate_operands(value, 2, "Remainder must have two operands");
}


/// \brief Exponentiation
class power_exprt:public binary_exprt
{
public:
  DEPRECATED("use power_exprt(lhs, rhs) instead")
  power_exprt():binary_exprt(ID_power)
  {
  }

  power_exprt(
    const exprt &_base,
    const exprt &_exp):
    binary_exprt(_base, ID_power, _exp)
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
  PRECONDITION(expr.id()==ID_power);
  DATA_INVARIANT(expr.operands().size()==2, "Power must have two operands");
  return static_cast<const power_exprt &>(expr);
}

/// \copydoc to_power_expr(const exprt &)
inline power_exprt &to_power_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_power);
  DATA_INVARIANT(expr.operands().size()==2, "Power must have two operands");
  return static_cast<power_exprt &>(expr);
}

template<> inline bool can_cast_expr<power_exprt>(const exprt &base)
{
  return base.id()==ID_power;
}
inline void validate_expr(const power_exprt &value)
{
  validate_operands(value, 2, "Power must have two operands");
}


/// \brief Falling factorial power
class factorial_power_exprt:public binary_exprt
{
public:
  DEPRECATED("use factorial_power_exprt(lhs, rhs) instead")
  factorial_power_exprt():binary_exprt(ID_factorial_power)
  {
  }

  factorial_power_exprt(
    const exprt &_base,
    const exprt &_exp):
    binary_exprt(_base, ID_factorial_power, _exp)
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
  PRECONDITION(expr.id()==ID_factorial_power);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Factorial power must have two operands");
  return static_cast<const factorial_power_exprt &>(expr);
}

/// \copydoc to_factorial_power_expr(const exprt &)
inline factorial_power_exprt &to_factorial_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_factorial_power);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Factorial power must have two operands");
  return static_cast<factorial_power_exprt &>(expr);
}

template<> inline bool can_cast_expr<factorial_power_exprt>(
  const exprt &base)
{
  return base.id()==ID_factorial_power;
}
inline void validate_expr(const factorial_power_exprt &value)
{
  validate_operands(value, 2, "Factorial power must have two operands");
}


/// \brief Equality
class equal_exprt:public binary_relation_exprt
{
public:
  DEPRECATED("use equal_exprt(lhs, rhs) instead")
  equal_exprt():binary_relation_exprt(ID_equal)
  {
  }

  equal_exprt(const exprt &_lhs, const exprt &_rhs):
    binary_relation_exprt(_lhs, ID_equal, _rhs)
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

template<> inline bool can_cast_expr<equal_exprt>(const exprt &base)
{
  return base.id()==ID_equal;
}
inline void validate_expr(const equal_exprt &value)
{
  validate_operands(value, 2, "Equality must have two operands");
}


/// \brief Disequality
class notequal_exprt:public binary_relation_exprt
{
public:
  DEPRECATED("use notequal_exprt(lhs, rhs) instead")
  notequal_exprt():binary_relation_exprt(ID_notequal)
  {
  }

  notequal_exprt(const exprt &_lhs, const exprt &_rhs):
    binary_relation_exprt(_lhs, ID_notequal, _rhs)
  {
  }
};

/// \brief Cast an exprt to an \ref notequal_exprt
///
/// \a expr must be known to be \ref notequal_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref notequal_exprt
inline const notequal_exprt &to_notequal_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_notequal);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Inequality must have two operands");
  return static_cast<const notequal_exprt &>(expr);
}

/// \copydoc to_notequal_expr(const exprt &)
inline notequal_exprt &to_notequal_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_notequal);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Inequality must have two operands");
  return static_cast<notequal_exprt &>(expr);
}

template<> inline bool can_cast_expr<notequal_exprt>(const exprt &base)
{
  return base.id()==ID_notequal;
}
inline void validate_expr(const notequal_exprt &value)
{
  validate_operands(value, 2, "Inequality must have two operands");
}


/// \brief Array index operator
class index_exprt:public binary_exprt
{
public:
  DEPRECATED("use index_exprt(array, index) instead")
  index_exprt():binary_exprt(ID_index)
  {
  }

  DEPRECATED("use index_exprt(array, index) instead")
  explicit index_exprt(const typet &_type):binary_exprt(ID_index, _type)
  {
  }

  index_exprt(const exprt &_array, const exprt &_index):
    binary_exprt(_array, ID_index, _index, _array.type().subtype())
  {
  }

  index_exprt(
    const exprt &_array,
    const exprt &_index,
    const typet &_type):
    binary_exprt(_array, ID_index, _index, _type)
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

/// \brief Cast an exprt to an \ref index_exprt
///
/// \a expr must be known to be \ref index_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref index_exprt
inline const index_exprt &to_index_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_index);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Array index must have two operands");
  return static_cast<const index_exprt &>(expr);
}

/// \copydoc to_index_expr(const exprt &)
inline index_exprt &to_index_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_index);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Array index must have two operands");
  return static_cast<index_exprt &>(expr);
}

template<> inline bool can_cast_expr<index_exprt>(const exprt &base)
{
  return base.id()==ID_index;
}
inline void validate_expr(const index_exprt &value)
{
  validate_operands(value, 2, "Array index must have two operands");
}


/// \brief Array constructor from single element
class array_of_exprt:public unary_exprt
{
public:
  DEPRECATED("use array_of_exprt(what, type) instead")
  array_of_exprt():unary_exprt(ID_array_of)
  {
  }

  explicit array_of_exprt(
    const exprt &_what, const array_typet &_type):
    unary_exprt(ID_array_of, _what, _type)
  {
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

/// \brief Cast an exprt to an \ref array_of_exprt
///
/// \a expr must be known to be \ref array_of_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref array_of_exprt
inline const array_of_exprt &to_array_of_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_array_of);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "'Array of' must have one operand");
  return static_cast<const array_of_exprt &>(expr);
}

/// \copydoc to_array_of_expr(const exprt &)
inline array_of_exprt &to_array_of_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_array_of);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "'Array of' must have one operand");
  return static_cast<array_of_exprt &>(expr);
}

template<> inline bool can_cast_expr<array_of_exprt>(const exprt &base)
{
  return base.id()==ID_array_of;
}
inline void validate_expr(const array_of_exprt &value)
{
  validate_operands(value, 1, "'Array of' must have one operand");
}


/// \brief Array constructor from list of elements
class array_exprt : public multi_ary_exprt
{
public:
  DEPRECATED("use array_exprt(type) instead")
  array_exprt() : multi_ary_exprt(ID_array)
  {
  }

  explicit array_exprt(const array_typet &_type)
    : multi_ary_exprt(ID_array, _type)
  {
  }
};

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

template<> inline bool can_cast_expr<array_exprt>(const exprt &base)
{
  return base.id()==ID_array;
}

/// Array constructor from a list of index-element pairs
/// Operands are index/value pairs, alternating.
class array_list_exprt : public multi_ary_exprt
{
public:
  explicit array_list_exprt(const array_typet &_type)
    : multi_ary_exprt(ID_array_list, _type)
  {
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

/// \brief Vector constructor from list of elements
class vector_exprt : public multi_ary_exprt
{
public:
  DEPRECATED("use vector_exprt(type) instead")
  vector_exprt() : multi_ary_exprt(ID_vector)
  {
  }

  explicit vector_exprt(const vector_typet &_type)
    : multi_ary_exprt(ID_vector, _type)
  {
  }
};

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

template<> inline bool can_cast_expr<vector_exprt>(const exprt &base)
{
  return base.id()==ID_vector;
}


/// \brief Union constructor from single element
class union_exprt:public unary_exprt
{
public:
  DEPRECATED("use union_exprt(component_name, value, type) instead")
  union_exprt():unary_exprt(ID_union)
  {
  }

  DEPRECATED("use union_exprt(component_name, value, type) instead")
  explicit union_exprt(const typet &_type):
    unary_exprt(ID_union, _type)
  {
  }

  union_exprt(
    const irep_idt &_component_name,
    const exprt &_value,
    const typet &_type)
    : unary_exprt(ID_union, _value, _type)
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
    set(ID_component_number, component_number);
  }
};

/// \brief Cast an exprt to a \ref union_exprt
///
/// \a expr must be known to be \ref union_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref union_exprt
inline const union_exprt &to_union_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_union);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Union constructor must have one operand");
  return static_cast<const union_exprt &>(expr);
}

/// \copydoc to_union_expr(const exprt &)
inline union_exprt &to_union_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_union);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Union constructor must have one operand");
  return static_cast<union_exprt &>(expr);
}

template<> inline bool can_cast_expr<union_exprt>(const exprt &base)
{
  return base.id()==ID_union;
}
inline void validate_expr(const union_exprt &value)
{
  validate_operands(value, 1, "Union constructor must have one operand");
}


/// \brief Struct constructor from list of elements
class struct_exprt : public multi_ary_exprt
{
public:
  DEPRECATED("use struct_exprt(component_name, value, type) instead")
  struct_exprt() : multi_ary_exprt(ID_struct)
  {
  }

  explicit struct_exprt(const typet &_type) : multi_ary_exprt(ID_struct, _type)
  {
  }

  exprt &component(const irep_idt &name, const namespacet &ns);
  const exprt &component(const irep_idt &name, const namespacet &ns) const;
};

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

template<> inline bool can_cast_expr<struct_exprt>(const exprt &base)
{
  return base.id()==ID_struct;
}


/// \brief Complex constructor from a pair of numbers
class complex_exprt:public binary_exprt
{
public:
  DEPRECATED("use complex_exprt(r, i, type) instead")
  complex_exprt():binary_exprt(ID_complex)
  {
  }

  DEPRECATED("use complex_exprt(r, i, type) instead")
  explicit complex_exprt(const complex_typet &_type):
    binary_exprt(ID_complex, _type)
  {
  }

  complex_exprt(
    const exprt &_real,
    const exprt &_imag,
    const complex_typet &_type)
    : binary_exprt(_real, ID_complex, _imag, _type)
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

/// \brief Cast an exprt to a \ref complex_exprt
///
/// \a expr must be known to be \ref complex_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref complex_exprt
inline const complex_exprt &to_complex_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_complex);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Complex constructor must have two operands");
  return static_cast<const complex_exprt &>(expr);
}

/// \copydoc to_complex_expr(const exprt &)
inline complex_exprt &to_complex_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_complex);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Complex constructor must have two operands");
  return static_cast<complex_exprt &>(expr);
}

template<> inline bool can_cast_expr<complex_exprt>(const exprt &base)
{
  return base.id()==ID_complex;
}
inline void validate_expr(const complex_exprt &value)
{
  validate_operands(value, 2, "Complex constructor must have two operands");
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

/// \brief Cast an exprt to a \ref complex_real_exprt
///
/// \a expr must be known to be a \ref complex_real_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref complex_real_exprt
inline const complex_real_exprt &to_complex_real_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_complex_real);
  DATA_INVARIANT(
    expr.operands().size() == 1,
    "real part retrieval operation must have one operand");
  return static_cast<const complex_real_exprt &>(expr);
}

/// \copydoc to_complex_real_expr(const exprt &)
inline complex_real_exprt &to_complex_real_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_complex_real);
  DATA_INVARIANT(
    expr.operands().size() == 1,
    "real part retrieval operation must have one operand");
  return static_cast<complex_real_exprt &>(expr);
}

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

/// \brief Imaginary part of the expression describing a complex number.
class complex_imag_exprt : public unary_exprt
{
public:
  explicit complex_imag_exprt(const exprt &op)
    : unary_exprt(ID_complex_imag, op, to_complex_type(op.type()).subtype())
  {
  }
};

/// \brief Cast an exprt to a \ref complex_imag_exprt
///
/// \a expr must be known to be a \ref complex_imag_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref complex_imag_exprt
inline const complex_imag_exprt &to_complex_imag_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_complex_imag);
  DATA_INVARIANT(
    expr.operands().size() == 1,
    "imaginary part retrieval operation must have one operand");
  return static_cast<const complex_imag_exprt &>(expr);
}

/// \copydoc to_complex_imag_expr(const exprt &)
inline complex_imag_exprt &to_complex_imag_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_complex_imag);
  DATA_INVARIANT(
    expr.operands().size() == 1,
    "imaginary part retrieval operation must have one operand");
  return static_cast<complex_imag_exprt &>(expr);
}

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

class namespacet;

/// \brief Split an expression into a base object and a (byte) offset
class object_descriptor_exprt:public binary_exprt
{
public:
  object_descriptor_exprt()
    : binary_exprt(exprt(ID_unknown), ID_object_descriptor, exprt(ID_unknown))
  {
  }

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
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Object descriptor must have two operands");
  return static_cast<const object_descriptor_exprt &>(expr);
}

/// \copydoc to_object_descriptor_expr(const exprt &)
inline object_descriptor_exprt &to_object_descriptor_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_object_descriptor);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Object descriptor must have two operands");
  return static_cast<object_descriptor_exprt &>(expr);
}

template<>
inline bool can_cast_expr<object_descriptor_exprt>(const exprt &base)
{
  return base.id()==ID_object_descriptor;
}
inline void validate_expr(const object_descriptor_exprt &value)
{
  validate_operands(value, 2, "Object descriptor must have two operands");
}


/// Representation of heap-allocated objects
class dynamic_object_exprt:public binary_exprt
{
public:
  dynamic_object_exprt()
    : binary_exprt(exprt(ID_unknown), ID_dynamic_object, exprt(ID_unknown))
  {
  }

  explicit dynamic_object_exprt(const typet &type)
    : binary_exprt(
        exprt(ID_unknown),
        ID_dynamic_object,
        exprt(ID_unknown),
        type)
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
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Dynamic object must have two operands");
  return static_cast<const dynamic_object_exprt &>(expr);
}

/// \copydoc to_dynamic_object_expr(const exprt &)
inline dynamic_object_exprt &to_dynamic_object_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_dynamic_object);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Dynamic object must have two operands");
  return static_cast<dynamic_object_exprt &>(expr);
}

template<> inline bool can_cast_expr<dynamic_object_exprt>(const exprt &base)
{
  return base.id()==ID_dynamic_object;
}

inline void validate_expr(const dynamic_object_exprt &value)
{
  validate_operands(value, 2, "Dynamic object must have two operands");
}


/// \brief Semantic type conversion
class typecast_exprt:public unary_exprt
{
public:
  DEPRECATED("use typecast_exprt(op, type) instead")
  explicit typecast_exprt(const typet &_type):unary_exprt(ID_typecast, _type)
  {
  }

  typecast_exprt(const exprt &op, const typet &_type):
    unary_exprt(ID_typecast, op, _type)
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

/// \brief Cast an exprt to a \ref typecast_exprt
///
/// \a expr must be known to be \ref typecast_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref typecast_exprt
inline const typecast_exprt &to_typecast_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_typecast);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Typecast must have one operand");
  return static_cast<const typecast_exprt &>(expr);
}

/// \copydoc to_typecast_expr(const exprt &)
inline typecast_exprt &to_typecast_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_typecast);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Typecast must have one operand");
  return static_cast<typecast_exprt &>(expr);
}

template<> inline bool can_cast_expr<typecast_exprt>(const exprt &base)
{
  return base.id()==ID_typecast;
}
inline void validate_expr(const typecast_exprt &value)
{
  validate_operands(value, 1, "Typecast must have one operand");
}


/// \brief Semantic type conversion from/to floating-point formats
class floatbv_typecast_exprt:public binary_exprt
{
public:
  DEPRECATED("use floatbv_typecast_exprt(op, r, type) instead")
  floatbv_typecast_exprt():binary_exprt(ID_floatbv_typecast)
  {
  }

  floatbv_typecast_exprt(
    const exprt &op,
    const exprt &rounding,
    const typet &_type):binary_exprt(op, ID_floatbv_typecast, rounding, _type)
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

/// \brief Cast an exprt to a \ref floatbv_typecast_exprt
///
/// \a expr must be known to be \ref floatbv_typecast_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref floatbv_typecast_exprt
inline const floatbv_typecast_exprt &to_floatbv_typecast_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_floatbv_typecast);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Float typecast must have two operands");
  return static_cast<const floatbv_typecast_exprt &>(expr);
}

/// \copydoc to_floatbv_typecast_expr(const exprt &)
inline floatbv_typecast_exprt &to_floatbv_typecast_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_floatbv_typecast);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Float typecast must have two operands");
  return static_cast<floatbv_typecast_exprt &>(expr);
}

template<>
inline bool can_cast_expr<floatbv_typecast_exprt>(const exprt &base)
{
  return base.id()==ID_floatbv_typecast;
}
inline void validate_expr(const floatbv_typecast_exprt &value)
{
  validate_operands(value, 2, "Float typecast must have two operands");
}


/// \brief Boolean AND
class and_exprt:public multi_ary_exprt
{
public:
  and_exprt():multi_ary_exprt(ID_and, bool_typet())
  {
  }

  and_exprt(const exprt &op0, const exprt &op1):
    multi_ary_exprt(op0, ID_and, op1, bool_typet())
  {
  }

  and_exprt(const exprt &op0, const exprt &op1, const exprt &op2)
    : multi_ary_exprt(ID_and, {op0, op1, op2}, bool_typet())
  {
  }

  and_exprt(
    const exprt &op0,
    const exprt &op1,
    const exprt &op2,
    const exprt &op3)
    : multi_ary_exprt(ID_and, {op0, op1, op2, op3}, bool_typet())
  {
  }
};

/// 1) generates a conjunction for two or more operands
/// 2) for one operand, returns the operand
/// 3) returns true otherwise

exprt conjunction(const exprt::operandst &);

/// \brief Cast an exprt to a \ref and_exprt
///
/// \a expr must be known to be \ref and_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref and_exprt
inline const and_exprt &to_and_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_and);
  // DATA_INVARIANT(
  //   expr.operands().size()>=2,
  //   "And must have two or more operands");
  return static_cast<const and_exprt &>(expr);
}

/// \copydoc to_and_expr(const exprt &)
inline and_exprt &to_and_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_and);
  // DATA_INVARIANT(
  //   expr.operands().size()>=2,
  //   "And must have two or more operands");
  return static_cast<and_exprt &>(expr);
}

template<> inline bool can_cast_expr<and_exprt>(const exprt &base)
{
  return base.id()==ID_and;
}
// inline void validate_expr(const and_exprt &value)
// {
//   validate_operands(value, 2, "And must have two or more operands", true);
// }


/// \brief Boolean implication
class implies_exprt:public binary_exprt
{
public:
  DEPRECATED("use implies_exprt(a, b) instead")
  implies_exprt():binary_exprt(ID_implies, bool_typet())
  {
  }

  implies_exprt(const exprt &op0, const exprt &op1):
    binary_exprt(op0, ID_implies, op1, bool_typet())
  {
  }
};

/// \brief Cast an exprt to a \ref implies_exprt
///
/// \a expr must be known to be \ref implies_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref implies_exprt
inline const implies_exprt &to_implies_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_implies);
  DATA_INVARIANT(expr.operands().size()==2, "Implies must have two operands");
  return static_cast<const implies_exprt &>(expr);
}

/// \copydoc to_implies_expr(const exprt &)
inline implies_exprt &to_implies_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_implies);
  DATA_INVARIANT(expr.operands().size()==2, "Implies must have two operands");
  return static_cast<implies_exprt &>(expr);
}

template<> inline bool can_cast_expr<implies_exprt>(const exprt &base)
{
  return base.id()==ID_implies;
}
inline void validate_expr(const implies_exprt &value)
{
  validate_operands(value, 2, "Implies must have two operands");
}


/// \brief Boolean OR
class or_exprt:public multi_ary_exprt
{
public:
  or_exprt():multi_ary_exprt(ID_or, bool_typet())
  {
  }

  or_exprt(const exprt &op0, const exprt &op1):
    multi_ary_exprt(op0, ID_or, op1, bool_typet())
  {
  }

  or_exprt(const exprt &op0, const exprt &op1, const exprt &op2)
    : multi_ary_exprt(ID_or, {op0, op1, op2}, bool_typet())
  {
  }

  or_exprt(
    const exprt &op0,
    const exprt &op1,
    const exprt &op2,
    const exprt &op3)
    : multi_ary_exprt(ID_or, {op0, op1, op2, op3}, bool_typet())
  {
  }
};

/// 1) generates a disjunction for two or more operands
/// 2) for one operand, returns the operand
/// 3) returns false otherwise

exprt disjunction(const exprt::operandst &);

/// \brief Cast an exprt to a \ref or_exprt
///
/// \a expr must be known to be \ref or_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref or_exprt
inline const or_exprt &to_or_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_or);
  // DATA_INVARIANT(
  //   expr.operands().size()>=2,
  //   "Or must have two or more operands");
  return static_cast<const or_exprt &>(expr);
}

/// \copydoc to_or_expr(const exprt &)
inline or_exprt &to_or_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_or);
  // DATA_INVARIANT(
  //   expr.operands().size()>=2,
  //   "Or must have two or more operands");
  return static_cast<or_exprt &>(expr);
}

template<> inline bool can_cast_expr<or_exprt>(const exprt &base)
{
  return base.id()==ID_or;
}
// inline void validate_expr(const or_exprt &value)
// {
//   validate_operands(value, 2, "Or must have two or more operands", true);
// }


/// \brief Boolean XOR
class xor_exprt:public multi_ary_exprt
{
public:
  xor_exprt():multi_ary_exprt(ID_bitxor, bool_typet())
  {
  }

  xor_exprt(const exprt &_op0, const exprt &_op1):
    multi_ary_exprt(_op0, ID_xor, _op1, bool_typet())
  {
  }
};

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

template<> inline bool can_cast_expr<xor_exprt>(const exprt &base)
{
  return base.id()==ID_xor;
}
// inline void validate_expr(const bitxor_exprt &value)
// {
//   validate_operands(
//     value,
//     2,
//     "Bit-wise xor must have two or more operands",
//     true);
// }


/// \brief Bit-wise negation of bit-vectors
class bitnot_exprt:public unary_exprt
{
public:
  DEPRECATED("use bitnot_exprt(op) instead")
  bitnot_exprt():unary_exprt(ID_bitnot)
  {
  }

  explicit bitnot_exprt(const exprt &op):
    unary_exprt(ID_bitnot, op)
  {
  }
};

/// \brief Cast an exprt to a \ref bitnot_exprt
///
/// \a expr must be known to be \ref bitnot_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref bitnot_exprt
inline const bitnot_exprt &to_bitnot_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_bitnot);
  // DATA_INVARIANT(expr.operands().size()==1,
  //                "Bit-wise not must have one operand");
  return static_cast<const bitnot_exprt &>(expr);
}

/// \copydoc to_bitnot_expr(const exprt &)
inline bitnot_exprt &to_bitnot_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_bitnot);
  // DATA_INVARIANT(expr.operands().size()==1,
  //                "Bit-wise not must have one operand");
  return static_cast<bitnot_exprt &>(expr);
}

template<> inline bool can_cast_expr<bitnot_exprt>(const exprt &base)
{
  return base.id()==ID_bitnot;
}
// inline void validate_expr(const bitnot_exprt &value)
// {
//   validate_operands(value, 1, "Bit-wise not must have one operand");
// }


/// \brief Bit-wise OR
class bitor_exprt:public multi_ary_exprt
{
public:
  DEPRECATED("use bitor_exprt(op0, op1) instead")
  bitor_exprt():multi_ary_exprt(ID_bitor)
  {
  }

  bitor_exprt(const exprt &_op0, const exprt &_op1)
    : multi_ary_exprt(_op0, ID_bitor, _op1, _op0.type())
  {
  }
};

/// \brief Cast an exprt to a \ref bitor_exprt
///
/// \a expr must be known to be \ref bitor_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref bitor_exprt
inline const bitor_exprt &to_bitor_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_bitor);
  // DATA_INVARIANT(
  //   expr.operands().size()>=2,
  //   "Bit-wise or must have two or more operands");
  return static_cast<const bitor_exprt &>(expr);
}

/// \copydoc to_bitor_expr(const exprt &)
inline bitor_exprt &to_bitor_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_bitor);
  // DATA_INVARIANT(
  //   expr.operands().size()>=2,
  //   "Bit-wise or must have two or more operands");
  return static_cast<bitor_exprt &>(expr);
}

template<> inline bool can_cast_expr<bitor_exprt>(const exprt &base)
{
  return base.id()==ID_bitor;
}
// inline void validate_expr(const bitor_exprt &value)
// {
//   validate_operands(
//     value,
//     2,
//     "Bit-wise or must have two or more operands",
//     true);
// }


/// \brief Bit-wise XOR
class bitxor_exprt:public multi_ary_exprt
{
public:
  DEPRECATED("use bitxor_exprt(op0, op1) instead")
  bitxor_exprt():multi_ary_exprt(ID_bitxor)
  {
  }

  bitxor_exprt(const exprt &_op0, const exprt &_op1):
    multi_ary_exprt(_op0, ID_bitxor, _op1, _op0.type())
  {
  }
};

/// \brief Cast an exprt to a \ref bitxor_exprt
///
/// \a expr must be known to be \ref bitxor_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref bitxor_exprt
inline const bitxor_exprt &to_bitxor_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_bitxor);
  // DATA_INVARIANT(
  //   expr.operands().size()>=2,
  //   "Bit-wise xor must have two or more operands");
  return static_cast<const bitxor_exprt &>(expr);
}

/// \copydoc to_bitxor_expr(const exprt &)
inline bitxor_exprt &to_bitxor_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_bitxor);
  // DATA_INVARIANT(
  //   expr.operands().size()>=2,
  //   "Bit-wise xor must have two or more operands");
  return static_cast<bitxor_exprt &>(expr);
}

template<> inline bool can_cast_expr<bitxor_exprt>(const exprt &base)
{
  return base.id()==ID_bitxor;
}
// inline void validate_expr(const bitxor_exprt &value)
// {
//   validate_operands(
//     value,
//     2,
//     "Bit-wise xor must have two or more operands",
//     true);
// }


/// \brief Bit-wise AND
class bitand_exprt:public multi_ary_exprt
{
public:
  DEPRECATED("use bitand_exprt(op0, op1) instead")
  bitand_exprt():multi_ary_exprt(ID_bitand)
  {
  }

  bitand_exprt(const exprt &_op0, const exprt &_op1)
    : multi_ary_exprt(_op0, ID_bitand, _op1, _op0.type())
  {
  }
};

/// \brief Cast an exprt to a \ref bitand_exprt
///
/// \a expr must be known to be \ref bitand_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref bitand_exprt
inline const bitand_exprt &to_bitand_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_bitand);
  // DATA_INVARIANT(
  //   expr.operands().size()>=2,
  //   "Bit-wise and must have two or more operands");
  return static_cast<const bitand_exprt &>(expr);
}

/// \copydoc to_bitand_expr(const exprt &)
inline bitand_exprt &to_bitand_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_bitand);
  // DATA_INVARIANT(
  //   expr.operands().size()>=2,
  //   "Bit-wise and must have two or more operands");
  return static_cast<bitand_exprt &>(expr);
}

template<> inline bool can_cast_expr<bitand_exprt>(const exprt &base)
{
  return base.id()==ID_bitand;
}
// inline void validate_expr(const bitand_exprt &value)
// {
//   validate_operands(
//     value,
//     2,
//     "Bit-wise and must have two or more operands",
//     true);
// }


/// \brief A base class for shift operators
class shift_exprt:public binary_exprt
{
public:
  DEPRECATED("use shift_exprt(value, id, distance) instead")
  explicit shift_exprt(const irep_idt &_id):binary_exprt(_id)
  {
  }

  DEPRECATED("use shift_exprt(value, id, distance) instead")
  shift_exprt(const irep_idt &_id, const typet &_type):
    binary_exprt(_id, _type)
  {
  }

  shift_exprt(const exprt &_src, const irep_idt &_id, const exprt &_distance):
    binary_exprt(_src, _id, _distance)
  {
  }

  shift_exprt(
    const exprt &_src,
    const irep_idt &_id,
    const std::size_t _distance);

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

/// \brief Cast an exprt to a \ref shift_exprt
///
/// \a expr must be known to be \ref shift_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref shift_exprt
inline const shift_exprt &to_shift_expr(const exprt &expr)
{
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Shifts must have two operands");
  return static_cast<const shift_exprt &>(expr);
}

/// \copydoc to_shift_expr(const exprt &)
inline shift_exprt &to_shift_expr(exprt &expr)
{
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Shifts must have two operands");
  return static_cast<shift_exprt &>(expr);
}

// The to_*_expr function for this type doesn't do any checks before casting,
// therefore the implementation is essentially a static_cast.
// Enabling expr_dynamic_cast would hide this; instead use static_cast directly.
// inline void validate_expr(const shift_exprt &value)
// {
//   validate_operands(value, 2, "Shifts must have two operands");
// }


/// \brief Left shift
class shl_exprt:public shift_exprt
{
public:
  DEPRECATED("use shl_exprt(value, distance) instead")
  shl_exprt():shift_exprt(ID_shl)
  {
  }

  shl_exprt(const exprt &_src, const exprt &_distance):
    shift_exprt(_src, ID_shl, _distance)
  {
  }

  shl_exprt(const exprt &_src, const std::size_t _distance):
    shift_exprt(_src, ID_shl, _distance)
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
  DATA_INVARIANT(
    expr.operands().size() == 2, "Bit-wise shl must have two operands");
  return static_cast<const shl_exprt &>(expr);
}

/// \copydoc to_shl_expr(const exprt &)
inline shl_exprt &to_shl_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_shl);
  DATA_INVARIANT(
    expr.operands().size() == 2, "Bit-wise shl must have two operands");
  return static_cast<shl_exprt &>(expr);
}

/// \brief Arithmetic right shift
class ashr_exprt:public shift_exprt
{
public:
  DEPRECATED("use ashl_exprt(value, distance) instead")
  ashr_exprt():shift_exprt(ID_ashr)
  {
  }

  ashr_exprt(const exprt &_src, const exprt &_distance):
    shift_exprt(_src, ID_ashr, _distance)
  {
  }

  ashr_exprt(const exprt &_src, const std::size_t _distance):
    shift_exprt(_src, ID_ashr, _distance)
  {
  }
};

/// \brief Logical right shift
class lshr_exprt:public shift_exprt
{
public:
  DEPRECATED("use lshl_exprt(value, distance) instead")
  lshr_exprt():shift_exprt(ID_lshr)
  {
  }

  lshr_exprt(const exprt &_src, const exprt &_distance):
    shift_exprt(_src, ID_lshr, _distance)
  {
  }

  lshr_exprt(const exprt &_src, const std::size_t _distance):
    shift_exprt(_src, ID_lshr, _distance)
  {
  }
};

/// \brief Bit-vector replication
class replication_exprt:public binary_exprt
{
public:
  DEPRECATED("use replication_exprt(times, value) instead")
  replication_exprt():binary_exprt(ID_replication)
  {
  }

  DEPRECATED("use replication_exprt(times, value) instead")
  explicit replication_exprt(const typet &_type):
    binary_exprt(ID_replication, _type)
  {
  }

  replication_exprt(const exprt &_times, const exprt &_src):
    binary_exprt(_times, ID_replication, _src)
  {
  }

  exprt &times()
  {
    return op0();
  }

  const exprt &times() const
  {
    return op0();
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

/// \brief Cast an exprt to a \ref replication_exprt
///
/// \a expr must be known to be \ref replication_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref replication_exprt
inline const replication_exprt &to_replication_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_replication);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Bit-wise replication must have two operands");
  return static_cast<const replication_exprt &>(expr);
}

/// \copydoc to_replication_expr(const exprt &)
inline replication_exprt &to_replication_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_replication);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Bit-wise replication must have two operands");
  return static_cast<replication_exprt &>(expr);
}

template<> inline bool can_cast_expr<replication_exprt>(const exprt &base)
{
  return base.id()==ID_replication;
}
inline void validate_expr(const replication_exprt &value)
{
  validate_operands(value, 2, "Bit-wise replication must have two operands");
}


/// \brief Extracts a single bit of a bit-vector operand
class extractbit_exprt:public binary_predicate_exprt
{
public:
  DEPRECATED("use extractbit_exprt(value, index) instead")
  extractbit_exprt():binary_predicate_exprt(ID_extractbit)
  {
  }

  /// Extract the \p _index-th least significant bit from \p _src.
  extractbit_exprt(
    const exprt &_src,
    const exprt &_index):binary_predicate_exprt(_src, ID_extractbit, _index)
  {
  }

  /// \copydoc extractbit_exprt(const exprt &, const exprt &)
  extractbit_exprt(
    const exprt &_src,
    const std::size_t _index);

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

/// \brief Cast an exprt to an \ref extractbit_exprt
///
/// \a expr must be known to be \ref extractbit_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref extractbit_exprt
inline const extractbit_exprt &to_extractbit_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_extractbit);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Extract bit must have two operands");
  return static_cast<const extractbit_exprt &>(expr);
}

/// \copydoc to_extractbit_expr(const exprt &)
inline extractbit_exprt &to_extractbit_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_extractbit);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Extract bit must have two operands");
  return static_cast<extractbit_exprt &>(expr);
}

template<> inline bool can_cast_expr<extractbit_exprt>(const exprt &base)
{
  return base.id()==ID_extractbit;
}
inline void validate_expr(const extractbit_exprt &value)
{
  validate_operands(value, 2, "Extract bit must have two operands");
}


/// \brief Extracts a sub-range of a bit-vector operand
class extractbits_exprt:public exprt
{
public:
  DEPRECATED("use extractbits_exprt(value, upper, lower) instead")
  extractbits_exprt():exprt(ID_extractbits)
  {
    operands().resize(3);
  }

  /// Extract the bits [\p _lower .. \p _upper] from \p _src to produce a result
  /// of type \p _type. Note that this specifies a closed interval, i.e., both
  /// bits \p _lower and \p _upper are included. Indices count from the
  /// least-significant bit, and are not affected by endianness.
  /// The ordering upper-lower matches what SMT-LIB uses.
  extractbits_exprt(
    const exprt &_src,
    const exprt &_upper,
    const exprt &_lower,
    const typet &_type):exprt(ID_extractbits, _type)
  {
    add_to_operands(_src, _upper, _lower);
  }

  // NOLINTNEXTLINE(whitespace/line_length)
  /// \copydoc extractbits_exprt(const exprt &, const exprt &, const exprt &, const typet &)
  extractbits_exprt(
    const exprt &_src,
    const std::size_t _upper,
    const std::size_t _lower,
    const typet &_type);

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

/// \brief Cast an exprt to an \ref extractbits_exprt
///
/// \a expr must be known to be \ref extractbits_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref extractbits_exprt
inline const extractbits_exprt &to_extractbits_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_extractbits);
  DATA_INVARIANT(
    expr.operands().size()==3,
    "Extract bits must have three operands");
  return static_cast<const extractbits_exprt &>(expr);
}

/// \copydoc to_extractbits_expr(const exprt &)
inline extractbits_exprt &to_extractbits_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_extractbits);
  DATA_INVARIANT(
    expr.operands().size()==3,
    "Extract bits must have three operands");
  return static_cast<extractbits_exprt &>(expr);
}

template<> inline bool can_cast_expr<extractbits_exprt>(const exprt &base)
{
  return base.id()==ID_extractbits;
}
inline void validate_expr(const extractbits_exprt &value)
{
  validate_operands(value, 3, "Extract bits must have three operands");
}


/// \brief Operator to return the address of an object
class address_of_exprt:public unary_exprt
{
public:
  explicit address_of_exprt(const exprt &op);

  address_of_exprt(const exprt &op, const pointer_typet &_type):
    unary_exprt(ID_address_of, op, _type)
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

/// \brief Cast an exprt to an \ref address_of_exprt
///
/// \a expr must be known to be \ref address_of_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref address_of_exprt
inline const address_of_exprt &to_address_of_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_address_of);
  DATA_INVARIANT(expr.operands().size()==1, "Address of must have one operand");
  return static_cast<const address_of_exprt &>(expr);
}

/// \copydoc to_address_of_expr(const exprt &)
inline address_of_exprt &to_address_of_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_address_of);
  DATA_INVARIANT(expr.operands().size()==1, "Address of must have one operand");
  return static_cast<address_of_exprt &>(expr);
}

template<> inline bool can_cast_expr<address_of_exprt>(const exprt &base)
{
  return base.id()==ID_address_of;
}
inline void validate_expr(const address_of_exprt &value)
{
  validate_operands(value, 1, "Address of must have one operand");
}


/// \brief Boolean negation
class not_exprt:public unary_exprt
{
public:
  explicit not_exprt(const exprt &op):
    unary_exprt(ID_not, op) // type from op.type()
  {
    PRECONDITION(op.type().id()==ID_bool);
  }

  not_exprt():unary_exprt(ID_not, bool_typet())
  {
  }
};

/// \brief Cast an exprt to an \ref not_exprt
///
/// \a expr must be known to be \ref not_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref not_exprt
inline const not_exprt &to_not_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_not);
  DATA_INVARIANT(expr.operands().size()==1, "Not must have one operand");
  return static_cast<const not_exprt &>(expr);
}

/// \copydoc to_not_expr(const exprt &)
inline not_exprt &to_not_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_not);
  DATA_INVARIANT(expr.operands().size()==1, "Not must have one operand");
  return static_cast<not_exprt &>(expr);
}

template<> inline bool can_cast_expr<not_exprt>(const exprt &base)
{
  return base.id()==ID_not;
}

inline void validate_expr(const not_exprt &value)
{
  validate_operands(value, 1, "Not must have one operand");
}


/// \brief Operator to dereference a pointer
class dereference_exprt:public unary_exprt
{
public:
  DEPRECATED("use dereference_exprt(pointer) instead")
  dereference_exprt():unary_exprt(ID_dereference)
  {
  }

  DEPRECATED("use dereference_exprt(pointer) instead")
  explicit dereference_exprt(const typet &type):
    unary_exprt(ID_dereference, type)
  {
  }

  explicit dereference_exprt(const exprt &op):
    unary_exprt(ID_dereference, op, op.type().subtype())
  {
    PRECONDITION(op.type().id()==ID_pointer);
  }

  dereference_exprt(const exprt &op, const typet &type):
    unary_exprt(ID_dereference, op, type)
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
};

/// \brief Cast an exprt to a \ref dereference_exprt
///
/// \a expr must be known to be \ref dereference_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref dereference_exprt
inline const dereference_exprt &to_dereference_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_dereference);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Dereference must have one operand");
  return static_cast<const dereference_exprt &>(expr);
}

/// \copydoc to_dereference_expr(const exprt &)
inline dereference_exprt &to_dereference_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_dereference);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Dereference must have one operand");
  return static_cast<dereference_exprt &>(expr);
}

template<> inline bool can_cast_expr<dereference_exprt>(const exprt &base)
{
  return base.id()==ID_dereference;
}
inline void validate_expr(const dereference_exprt &value)
{
  validate_operands(value, 1, "Dereference must have one operand");
}


/// \brief The trinary if-then-else operator
class if_exprt : public ternary_exprt
{
public:
  if_exprt(const exprt &cond, const exprt &t, const exprt &f)
    : ternary_exprt(ID_if, cond, t, f, t.type())
  {
  }

  if_exprt(const exprt &cond, const exprt &t, const exprt &f, const typet &type)
    : ternary_exprt(ID_if, cond, t, f, type)
  {
  }

  DEPRECATED("use if_exprt(cond, t, f) instead")
  if_exprt() : ternary_exprt(ID_if)
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

/// \brief Cast an exprt to an \ref if_exprt
///
/// \a expr must be known to be \ref if_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref if_exprt
inline const if_exprt &to_if_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_if);
  DATA_INVARIANT(
    expr.operands().size()==3,
    "If-then-else must have three operands");
  return static_cast<const if_exprt &>(expr);
}

/// \copydoc to_if_expr(const exprt &)
inline if_exprt &to_if_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_if);
  DATA_INVARIANT(
    expr.operands().size()==3,
    "If-then-else must have three operands");
  return static_cast<if_exprt &>(expr);
}

template<> inline bool can_cast_expr<if_exprt>(const exprt &base)
{
  return base.id()==ID_if;
}
inline void validate_expr(const if_exprt &value)
{
  validate_operands(value, 3, "If-then-else must have three operands");
}

/// \brief Operator to update elements in structs and arrays
/// \remark This expression will eventually be replaced by separate
///   array and struct update operators.
class with_exprt:public exprt
{
public:
  with_exprt(
    const exprt &_old,
    const exprt &_where,
    const exprt &_new_value):
    exprt(ID_with, _old.type())
  {
    add_to_operands(_old, _where, _new_value);
  }

  DEPRECATED("use with_exprt(old, where, new_value) instead")
  with_exprt():exprt(ID_with)
  {
    operands().resize(3);
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

/// \brief Cast an exprt to a \ref with_exprt
///
/// \a expr must be known to be \ref with_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref with_exprt
inline const with_exprt &to_with_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_with);
  DATA_INVARIANT(
    expr.operands().size()==3,
    "Array/structure update must have three operands");
  return static_cast<const with_exprt &>(expr);
}

/// \copydoc to_with_expr(const exprt &)
inline with_exprt &to_with_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_with);
  DATA_INVARIANT(
    expr.operands().size()==3,
    "Array/structure update must have three operands");
  return static_cast<with_exprt &>(expr);
}

template<> inline bool can_cast_expr<with_exprt>(const exprt &base)
{
  return base.id()==ID_with;
}
inline void validate_expr(const with_exprt &value)
{
  validate_operands(
    value,
    3,
    "Array/structure update must have three operands");
}


class index_designatort:public exprt
{
public:
  explicit index_designatort(const exprt &_index):
    exprt(ID_index_designator)
  {
    add_to_operands(_index);
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

/// \brief Cast an exprt to an \ref index_designatort
///
/// \a expr must be known to be \ref index_designatort.
///
/// \param expr: Source expression
/// \return Object of type \ref index_designatort
inline const index_designatort &to_index_designator(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_index_designator);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Index designator must have one operand");
  return static_cast<const index_designatort &>(expr);
}

/// \copydoc to_index_designator(const exprt &)
inline index_designatort &to_index_designator(exprt &expr)
{
  PRECONDITION(expr.id()==ID_index_designator);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Index designator must have one operand");
  return static_cast<index_designatort &>(expr);
}

template<> inline bool can_cast_expr<index_designatort>(const exprt &base)
{
  return base.id()==ID_index_designator;
}
inline void validate_expr(const index_designatort &value)
{
  validate_operands(value, 1, "Index designator must have one operand");
}


class member_designatort:public exprt
{
public:
  explicit member_designatort(const irep_idt &_component_name):
    exprt(ID_member_designator)
  {
    set(ID_component_name, _component_name);
  }

  irep_idt get_component_name() const
  {
    return get(ID_component_name);
  }
};

/// \brief Cast an exprt to an \ref member_designatort
///
/// \a expr must be known to be \ref member_designatort.
///
/// \param expr: Source expression
/// \return Object of type \ref member_designatort
inline const member_designatort &to_member_designator(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_member_designator);
  DATA_INVARIANT(
    !expr.has_operands(),
    "Member designator must not have operands");
  return static_cast<const member_designatort &>(expr);
}

/// \copydoc to_member_designator(const exprt &)
inline member_designatort &to_member_designator(exprt &expr)
{
  PRECONDITION(expr.id()==ID_member_designator);
  DATA_INVARIANT(
    !expr.has_operands(),
    "Member designator must not have operands");
  return static_cast<member_designatort &>(expr);
}

template<> inline bool can_cast_expr<member_designatort>(const exprt &base)
{
  return base.id()==ID_member_designator;
}
inline void validate_expr(const member_designatort &value)
{
  validate_operands(value, 0, "Member designator must not have operands");
}


/// \brief Operator to update elements in structs and arrays
class update_exprt : public ternary_exprt
{
public:
  update_exprt(
    const exprt &_old,
    const exprt &_designator,
    const exprt &_new_value)
    : ternary_exprt(ID_update, _old, _designator, _new_value, _old.type())
  {
  }

  DEPRECATED("use update_exprt(old, where, new_value) instead")
  explicit update_exprt(const typet &_type) : ternary_exprt(ID_update, _type)
  {
  }

  DEPRECATED("use update_exprt(old, where, new_value) instead")
  update_exprt() : ternary_exprt(ID_update)
  {
    op1().id(ID_designator);
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

/// \brief Cast an exprt to an \ref update_exprt
///
/// \a expr must be known to be \ref update_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref update_exprt
inline const update_exprt &to_update_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_update);
  DATA_INVARIANT(
    expr.operands().size()==3,
    "Array/structure update must have three operands");
  return static_cast<const update_exprt &>(expr);
}

/// \copydoc to_update_expr(const exprt &)
inline update_exprt &to_update_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_update);
  DATA_INVARIANT(
    expr.operands().size()==3,
    "Array/structure update must have three operands");
  return static_cast<update_exprt &>(expr);
}

template<> inline bool can_cast_expr<update_exprt>(const exprt &base)
{
  return base.id()==ID_update;
}
inline void validate_expr(const update_exprt &value)
{
  validate_operands(
    value,
    3,
    "Array/structure update must have three operands");
}


#if 0
/// \brief Update of one element of an array
class array_update_exprt:public exprt
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

  array_update_exprt():exprt(ID_array_update)
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

/// \brief Cast an exprt to an \ref array_update_exprt
///
/// \a expr must be known to be \ref array_update_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref array_update_exprt
inline const array_update_exprt &to_array_update_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_array_update);
  DATA_INVARIANT(
    expr.operands().size()==3,
    "Array update must have three operands");
  return static_cast<const array_update_exprt &>(expr);
}

/// \copydoc to_array_update_expr(const exprt &)
inline array_update_exprt &to_array_update_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_array_update);
  DATA_INVARIANT(
    expr.operands().size()==3,
    "Array update must have three operands");
  return static_cast<array_update_exprt &>(expr);
}

template<> inline bool can_cast_expr<array_update_exprt>(const exprt &base)
{
  return base.id()==ID_array_update;
}
inline void validate_expr(const array_update_exprt &value)
{
  validate_operands(value, 3, "Array update must have three operands");
}

#endif


/// \brief Extract member of struct or union
class member_exprt:public unary_exprt
{
public:
  member_exprt(
    const exprt &op,
    const irep_idt &component_name,
    const typet &_type):
    unary_exprt(ID_member, op, _type)
  {
    set_component_name(component_name);
  }

  member_exprt(
    const exprt &op,
    const struct_typet::componentt &c):
    unary_exprt(ID_member, op, c.type())
  {
    set_component_name(c.get_name());
  }

  DEPRECATED("use member_exprt(op, c) instead")
  member_exprt():unary_exprt(ID_member)
  {
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
};

/// \brief Cast an exprt to a \ref member_exprt
///
/// \a expr must be known to be \ref member_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref member_exprt
inline const member_exprt &to_member_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_member);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Extract member must have one operand");
  return static_cast<const member_exprt &>(expr);
}

/// \copydoc to_member_expr(const exprt &)
inline member_exprt &to_member_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_member);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Extract member must have one operand");
  return static_cast<member_exprt &>(expr);
}

template<> inline bool can_cast_expr<member_exprt>(const exprt &base)
{
  return base.id()==ID_member;
}
inline void validate_expr(const member_exprt &value)
{
  validate_operands(value, 1, "Extract member must have one operand");
}


/// \brief Evaluates to true if the operand is NaN
class isnan_exprt:public unary_predicate_exprt
{
public:
  explicit isnan_exprt(const exprt &op):
    unary_predicate_exprt(ID_isnan, op)
  {
  }

  DEPRECATED("use isnan_exprt(op) instead")
  isnan_exprt():unary_predicate_exprt(ID_isnan)
  {
  }
};

/// \brief Cast an exprt to a \ref isnan_exprt
///
/// \a expr must be known to be \ref isnan_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref isnan_exprt
inline const isnan_exprt &to_isnan_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_isnan);
  DATA_INVARIANT(expr.operands().size()==1, "Is NaN must have one operand");
  return static_cast<const isnan_exprt &>(expr);
}

/// \copydoc to_isnan_expr(const exprt &)
inline isnan_exprt &to_isnan_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_isnan);
  DATA_INVARIANT(expr.operands().size()==1, "Is NaN must have one operand");
  return static_cast<isnan_exprt &>(expr);
}

template<> inline bool can_cast_expr<isnan_exprt>(const exprt &base)
{
  return base.id()==ID_isnan;
}
inline void validate_expr(const isnan_exprt &value)
{
  validate_operands(value, 1, "Is NaN must have one operand");
}


/// \brief Evaluates to true if the operand is infinite
class isinf_exprt:public unary_predicate_exprt
{
public:
  explicit isinf_exprt(const exprt &op):
    unary_predicate_exprt(ID_isinf, op)
  {
  }

  DEPRECATED("use isinf_exprt(op) instead")
  isinf_exprt():unary_predicate_exprt(ID_isinf)
  {
  }
};

/// \brief Cast an exprt to a \ref isinf_exprt
///
/// \a expr must be known to be \ref isinf_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref isinf_exprt
inline const isinf_exprt &to_isinf_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_isinf);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Is infinite must have one operand");
  return static_cast<const isinf_exprt &>(expr);
}

/// \copydoc to_isinf_expr(const exprt &)
inline isinf_exprt &to_isinf_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_isinf);
  DATA_INVARIANT(
    expr.operands().size()==1,
    "Is infinite must have one operand");
  return static_cast<isinf_exprt &>(expr);
}

template<> inline bool can_cast_expr<isinf_exprt>(const exprt &base)
{
  return base.id()==ID_isinf;
}
inline void validate_expr(const isinf_exprt &value)
{
  validate_operands(value, 1, "Is infinite must have one operand");
}


/// \brief Evaluates to true if the operand is finite
class isfinite_exprt:public unary_predicate_exprt
{
public:
  explicit isfinite_exprt(const exprt &op):
    unary_predicate_exprt(ID_isfinite, op)
  {
  }

  DEPRECATED("use isfinite_exprt(op) instead")
  isfinite_exprt():unary_predicate_exprt(ID_isfinite)
  {
  }
};

/// \brief Cast an exprt to a \ref isfinite_exprt
///
/// \a expr must be known to be \ref isfinite_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref isfinite_exprt
inline const isfinite_exprt &to_isfinite_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_isfinite);
  DATA_INVARIANT(expr.operands().size()==1, "Is finite must have one operand");
  return static_cast<const isfinite_exprt &>(expr);
}

/// \copydoc to_isfinite_expr(const exprt &)
inline isfinite_exprt &to_isfinite_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_isfinite);
  DATA_INVARIANT(expr.operands().size()==1, "Is finite must have one operand");
  return static_cast<isfinite_exprt &>(expr);
}

template<> inline bool can_cast_expr<isfinite_exprt>(const exprt &base)
{
  return base.id()==ID_isfinite;
}
inline void validate_expr(const isfinite_exprt &value)
{
  validate_operands(value, 1, "Is finite must have one operand");
}


/// \brief Evaluates to true if the operand is a normal number
class isnormal_exprt:public unary_predicate_exprt
{
public:
  explicit isnormal_exprt(const exprt &op):
    unary_predicate_exprt(ID_isnormal, op)
  {
  }

  DEPRECATED("use isnormal_exprt(op) instead")
  isnormal_exprt():unary_predicate_exprt(ID_isnormal)
  {
  }
};

/// \brief Cast an exprt to a \ref isnormal_exprt
///
/// \a expr must be known to be \ref isnormal_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref isnormal_exprt
inline const isnormal_exprt &to_isnormal_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_isnormal);
  DATA_INVARIANT(expr.operands().size()==1, "Is normal must have one operand");
  return static_cast<const isnormal_exprt &>(expr);
}

/// \copydoc to_isnormal_expr(const exprt &)
inline isnormal_exprt &to_isnormal_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_isnormal);
  DATA_INVARIANT(expr.operands().size()==1, "Is normal must have one operand");
  return static_cast<isnormal_exprt &>(expr);
}

template<> inline bool can_cast_expr<isnormal_exprt>(const exprt &base)
{
  return base.id()==ID_isnormal;
}
inline void validate_expr(const isnormal_exprt &value)
{
  validate_operands(value, 1, "Is normal must have one operand");
}


/// \brief IEEE-floating-point equality
class ieee_float_equal_exprt:public binary_relation_exprt
{
public:
  DEPRECATED("use ieee_float_equal_exprt(lhs, rhs) instead")
  ieee_float_equal_exprt():binary_relation_exprt(ID_ieee_float_equal)
  {
  }

  ieee_float_equal_exprt(const exprt &_lhs, const exprt &_rhs):
    binary_relation_exprt(_lhs, ID_ieee_float_equal, _rhs)
  {
  }
};

/// \brief Cast an exprt to an \ref ieee_float_equal_exprt
///
/// \a expr must be known to be \ref ieee_float_equal_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref ieee_float_equal_exprt
inline const ieee_float_equal_exprt &to_ieee_float_equal_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_ieee_float_equal);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "IEEE equality must have two operands");
  return static_cast<const ieee_float_equal_exprt &>(expr);
}

/// \copydoc to_ieee_float_equal_expr(const exprt &)
inline ieee_float_equal_exprt &to_ieee_float_equal_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_ieee_float_equal);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "IEEE equality must have two operands");
  return static_cast<ieee_float_equal_exprt &>(expr);
}

template<>
inline bool can_cast_expr<ieee_float_equal_exprt>(const exprt &base)
{
  return base.id()==ID_ieee_float_equal;
}
inline void validate_expr(const ieee_float_equal_exprt &value)
{
  validate_operands(value, 2, "IEEE equality must have two operands");
}


/// \brief IEEE floating-point disequality
class ieee_float_notequal_exprt:public binary_relation_exprt
{
public:
  DEPRECATED("use ieee_float_notequal_exprt(lhs, rhs) instead")
  ieee_float_notequal_exprt():
    binary_relation_exprt(ID_ieee_float_notequal)
  {
  }

  ieee_float_notequal_exprt(const exprt &_lhs, const exprt &_rhs):
    binary_relation_exprt(_lhs, ID_ieee_float_notequal, _rhs)
  {
  }
};

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
  DATA_INVARIANT(
    expr.operands().size()==2,
    "IEEE inequality must have two operands");
  return static_cast<const ieee_float_notequal_exprt &>(expr);
}

/// \copydoc to_ieee_float_notequal_expr(const exprt &)
inline ieee_float_notequal_exprt &to_ieee_float_notequal_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_ieee_float_notequal);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "IEEE inequality must have two operands");
  return static_cast<ieee_float_notequal_exprt &>(expr);
}

template<>
inline bool can_cast_expr<ieee_float_notequal_exprt>(const exprt &base)
{
  return base.id()==ID_ieee_float_notequal;
}
inline void validate_expr(const ieee_float_notequal_exprt &value)
{
  validate_operands(value, 2, "IEEE inequality must have two operands");
}

/// \brief IEEE floating-point operations
/// These have two data operands (op0 and op1) and one rounding mode (op2).
/// The type of the result is that of the data operands.
class ieee_float_op_exprt:public exprt
{
public:
  DEPRECATED("use ieee_float_op_exprt(lhs, id, rhs, rm) instead")
  ieee_float_op_exprt()
  {
    operands().resize(3);
  }

  ieee_float_op_exprt(
    const exprt &_lhs,
    const irep_idt &_id,
    const exprt &_rhs,
    const exprt &_rm)
    : exprt(_id, _lhs.type())
  {
    add_to_operands(_lhs, _rhs, _rm);
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

/// \brief Cast an exprt to an \ref ieee_float_op_exprt
///
/// \a expr must be known to be \ref ieee_float_op_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref ieee_float_op_exprt
inline const ieee_float_op_exprt &to_ieee_float_op_expr(const exprt &expr)
{
  DATA_INVARIANT(
    expr.operands().size()==3,
    "IEEE float operations must have three arguments");
  return static_cast<const ieee_float_op_exprt &>(expr);
}

/// \copydoc to_ieee_float_op_expr(const exprt &)
inline ieee_float_op_exprt &to_ieee_float_op_expr(exprt &expr)
{
  DATA_INVARIANT(
    expr.operands().size()==3,
    "IEEE float operations must have three arguments");
  return static_cast<ieee_float_op_exprt &>(expr);
}

// The to_*_expr function for this type doesn't do any checks before casting,
// therefore the implementation is essentially a static_cast.
// Enabling expr_dynamic_cast would hide this; instead use static_cast directly.
// template<>
// inline void validate_expr<ieee_float_op_exprt>(
//   const ieee_float_op_exprt &value)
// {
//   validate_operands(
//     value,
//     3,
//     "IEEE float operations must have three arguments");
// }


/// \brief An expression denoting a type
class type_exprt : public nullary_exprt
{
public:
  DEPRECATED("use type_exprt(type) instead")
  type_exprt() : nullary_exprt(ID_type)
  {
  }

  explicit type_exprt(const typet &type) : nullary_exprt(ID_type, type)
  {
  }
};

/// \brief A constant literal expression
class constant_exprt:public exprt
{
public:
  DEPRECATED("use constant_exprt(value, type) instead")
  constant_exprt():exprt(ID_constant)
  {
  }

  DEPRECATED("use constant_exprt(value, type) instead")
  explicit constant_exprt(const typet &type):exprt(ID_constant, type)
  {
  }

  constant_exprt(const irep_idt &_value, const typet &_type):
    exprt(ID_constant, _type)
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

template<> inline bool can_cast_expr<constant_exprt>(const exprt &base)
{
  return base.id()==ID_constant;
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

/// \brief The null pointer constant
class null_pointer_exprt:public constant_exprt
{
public:
  explicit null_pointer_exprt(const pointer_typet &type)
    : constant_exprt(ID_NULL, type)
  {
  }
};

/// \brief Application of (mathematical) function
class function_application_exprt:public binary_exprt
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
inline const function_application_exprt &to_function_application_expr(
  const exprt &expr)
{
  PRECONDITION(expr.id()==ID_function_application);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Function application must have two operands");
  return static_cast<const function_application_exprt &>(expr);
}

/// \copydoc to_function_application_expr(const exprt &)
inline function_application_exprt &to_function_application_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_function_application);
  DATA_INVARIANT(
    expr.operands().size()==2,
    "Function application must have two operands");
  return static_cast<function_application_exprt &>(expr);
}

template<>
inline bool can_cast_expr<function_application_exprt>(const exprt &base)
{
  return base.id()==ID_function_application;
}
inline void validate_expr(const function_application_exprt &value)
{
  validate_operands(value, 2, "Function application must have two operands");
}

/// \brief Concatenation of bit-vector operands
///
/// This expression takes any number of operands
/// The ordering of the operands is the same as in the SMT-LIB 2 standard,
/// i.e., most-significant operands come first.
class concatenation_exprt : public multi_ary_exprt
{
public:
  DEPRECATED("use concatenation_exprt(op, type) instead")
  concatenation_exprt() : multi_ary_exprt(ID_concatenation)
  {
  }

  DEPRECATED("use concatenation_exprt(op, type) instead")
  explicit concatenation_exprt(const typet &_type)
    : multi_ary_exprt(ID_concatenation, _type)
  {
  }

  concatenation_exprt(const exprt &_op0, const exprt &_op1, const typet &_type)
    : multi_ary_exprt(_op0, ID_concatenation, _op1, _type)
  {
  }

  concatenation_exprt(operandst &&_operands, const typet &_type)
    : multi_ary_exprt(ID_concatenation, std::move(_operands), _type)
  {
  }
};

/// \brief Cast an exprt to a \ref concatenation_exprt
///
/// \a expr must be known to be \ref concatenation_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref concatenation_exprt
inline const concatenation_exprt &to_concatenation_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_concatenation);
  // DATA_INVARIANT(
  //   expr.operands().size()>=2,
  //   "Concatenation must have two or more operands");
  return static_cast<const concatenation_exprt &>(expr);
}

/// \copydoc to_concatenation_expr(const exprt &)
inline concatenation_exprt &to_concatenation_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_concatenation);
  // DATA_INVARIANT(
  //   expr.operands().size()>=2,
  //   "Concatenation must have two or more operands");
  return static_cast<concatenation_exprt &>(expr);
}

template<> inline bool can_cast_expr<concatenation_exprt>(const exprt &base)
{
  return base.id()==ID_concatenation;
}
// template<>
// inline void validate_expr<concatenation_exprt>(
//   const concatenation_exprt &value)
// {
//   validate_operands(
//     value,
//     2,
//     "Concatenation must have two or more operands",
//     true);
// }


/// \brief An expression denoting infinity
class infinity_exprt : public nullary_exprt
{
public:
  explicit infinity_exprt(const typet &_type)
    : nullary_exprt(ID_infinity, _type)
  {
  }
};

/// \brief A let expression
class let_exprt : public ternary_exprt
{
public:
  let_exprt(
    const symbol_exprt &symbol,
    const exprt &value,
    const exprt &where)
    : ternary_exprt(ID_let, symbol, value, where, where.type())
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

  exprt &value()
  {
    return op1();
  }

  const exprt &value() const
  {
    return op1();
  }

  exprt &where()
  {
    return op2();
  }

  const exprt &where() const
  {
    return op2();
  }
};

/// \brief Cast an exprt to a \ref let_exprt
///
/// \a expr must be known to be \ref let_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref let_exprt
inline const let_exprt &to_let_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_let);
  DATA_INVARIANT(expr.operands().size()==3, "Let must have three operands");
  return static_cast<const let_exprt &>(expr);
}

/// \copydoc to_let_expr(const exprt &)
inline let_exprt &to_let_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_let);
  DATA_INVARIANT(expr.operands().size()==3, "Let must have three operands");
  return static_cast<let_exprt &>(expr);
}

template<> inline bool can_cast_expr<let_exprt>(const exprt &base)
{
  return base.id()==ID_let;
}
inline void validate_expr(const let_exprt &value)
{
  validate_operands(value, 3, "Let must have three operands");
}

/// \brief A base class for quantifier expressions
class quantifier_exprt:public binary_predicate_exprt
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
  DATA_INVARIANT(expr.operands().size()==2,
                 "quantifier expressions must have two operands");
  DATA_INVARIANT(
    expr.op0().id() == ID_symbol, "quantified variable shall be a symbol");
  return static_cast<const quantifier_exprt &>(expr);
}

/// \copydoc to_quantifier_expr(const exprt &)
inline quantifier_exprt &to_quantifier_expr(exprt &expr)
{
  DATA_INVARIANT(expr.operands().size()==2,
                 "quantifier expressions must have two operands");
  DATA_INVARIANT(
    expr.op0().id() == ID_symbol, "quantified variable shall be a symbol");
  return static_cast<quantifier_exprt &>(expr);
}

template<> inline bool can_cast_expr<quantifier_exprt>(const exprt &base)
{
  return base.id() == ID_forall || base.id() == ID_exists;
}

inline void validate_expr(const quantifier_exprt &value)
{
  validate_operands(value, 2,
    "quantifier expressions must have two operands");
}

/// \brief A forall expression
class forall_exprt:public quantifier_exprt
{
public:
  forall_exprt(const symbol_exprt &_symbol, const exprt &_where)
    : quantifier_exprt(ID_forall, _symbol, _where)
  {
  }
};

/// \brief An exists expression
class exists_exprt:public quantifier_exprt
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

/// \brief The popcount (counting the number of bits set to 1) expression
class popcount_exprt: public unary_exprt
{
public:
  DEPRECATED("use popcount_exprt(op, type) instead")
  popcount_exprt(): unary_exprt(ID_popcount)
  {
  }

  popcount_exprt(const exprt &_op, const typet &_type)
    : unary_exprt(ID_popcount, _op, _type)
  {
  }

  explicit popcount_exprt(const exprt &_op)
    : unary_exprt(ID_popcount, _op, _op.type())
  {
  }
};

/// \brief Cast an exprt to a \ref popcount_exprt
///
/// \a expr must be known to be \ref popcount_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref popcount_exprt
inline const popcount_exprt &to_popcount_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_popcount);
  DATA_INVARIANT(expr.operands().size() == 1, "popcount must have one operand");
  return static_cast<const popcount_exprt &>(expr);
}

/// \copydoc to_popcount_expr(const exprt &)
inline popcount_exprt &to_popcount_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_popcount);
  DATA_INVARIANT(expr.operands().size() == 1, "popcount must have one operand");
  return static_cast<popcount_exprt &>(expr);
}

template <>
inline bool can_cast_expr<popcount_exprt>(const exprt &base)
{
  return base.id() == ID_popcount;
}
inline void validate_expr(const popcount_exprt &value)
{
  validate_operands(value, 1, "popcount must have one operand");
}

/// this is a parametric version of an if-expression: it returns
/// the value of the first case (using the ordering of the operands)
/// whose condition evaluates to true.
class cond_exprt : public multi_ary_exprt
{
public:
  explicit cond_exprt(const typet &_type) : multi_ary_exprt(ID_cond, _type)
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

/// \brief Cast an exprt to a \ref cond_exprt
///
/// \a expr must be known to be \ref cond_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref cond_exprt
inline const cond_exprt &to_cond_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_cond);
  DATA_INVARIANT(
    expr.operands().size() % 2 != 0, "cond must have even number of operands");
  return static_cast<const cond_exprt &>(expr);
}

/// \copydoc to_popcount_expr(const exprt &)
inline cond_exprt &to_cond_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_cond);
  DATA_INVARIANT(
    expr.operands().size() % 2 != 0, "cond must have even number of operands");
  return static_cast<cond_exprt &>(expr);
}

#endif // CPROVER_UTIL_STD_EXPR_H
