/*******************************************************************\

Module: API to expression classes for Pointers

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_POINTER_EXPR_H
#define CPROVER_UTIL_POINTER_EXPR_H

/// \file util/pointer_expr.h
/// API to expression classes for Pointers

#include "std_expr.h"

class namespacet;

/// \brief Split an expression into a base object and a (byte) offset
class object_descriptor_exprt : public binary_exprt
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
inline const object_descriptor_exprt &
to_object_descriptor_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_object_descriptor);
  const object_descriptor_exprt &ret =
    static_cast<const object_descriptor_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_object_descriptor_expr(const exprt &)
inline object_descriptor_exprt &to_object_descriptor_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_object_descriptor);
  object_descriptor_exprt &ret = static_cast<object_descriptor_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// Representation of heap-allocated objects
class dynamic_object_exprt : public binary_exprt
{
public:
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
inline const dynamic_object_exprt &to_dynamic_object_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_dynamic_object);
  const dynamic_object_exprt &ret =
    static_cast<const dynamic_object_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_dynamic_object_expr(const exprt &)
inline dynamic_object_exprt &to_dynamic_object_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_dynamic_object);
  dynamic_object_exprt &ret = static_cast<dynamic_object_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// Evaluates to true if the operand is a pointer to a dynamic object.
class is_dynamic_object_exprt : public unary_predicate_exprt
{
public:
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

/// \brief Operator to return the address of an object
class address_of_exprt : public unary_exprt
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
  PRECONDITION(expr.id() == ID_address_of);
  const address_of_exprt &ret = static_cast<const address_of_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_address_of_expr(const exprt &)
inline address_of_exprt &to_address_of_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_address_of);
  address_of_exprt &ret = static_cast<address_of_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Operator to dereference a pointer
class dereference_exprt : public unary_exprt
{
public:
  explicit dereference_exprt(const exprt &op)
    : unary_exprt(ID_dereference, op, op.type().subtype())
  {
    PRECONDITION(op.type().id() == ID_pointer);
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
  PRECONDITION(expr.id() == ID_dereference);
  const dereference_exprt &ret = static_cast<const dereference_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_dereference_expr(const exprt &)
inline dereference_exprt &to_dereference_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_dereference);
  dereference_exprt &ret = static_cast<dereference_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

#endif // CPROVER_UTIL_POINTER_EXPR_H
