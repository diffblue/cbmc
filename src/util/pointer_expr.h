/*******************************************************************\

Module: API to expression classes for Pointers

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_POINTER_EXPR_H
#define CPROVER_UTIL_POINTER_EXPR_H

/// \file util/pointer_expr.h
/// API to expression classes for Pointers

#include "bitvector_types.h"
#include "std_expr.h"

class namespacet;

/// The pointer type
/// These are both 'bitvector_typet' (they have a width)
/// and 'type_with_subtypet' (they have a subtype)
class pointer_typet : public bitvector_typet
{
public:
  pointer_typet(typet _base_type, std::size_t width)
    : bitvector_typet(ID_pointer, width)
  {
    subtype().swap(_base_type);
  }

  /// The type of the data what we point to.
  /// This method is preferred over .subtype(),
  /// which will eventually be deprecated.
  const typet &base_type() const
  {
    return subtype();
  }

  /// The type of the data what we point to.
  /// This method is preferred over .subtype(),
  /// which will eventually be deprecated.
  typet &base_type()
  {
    return subtype();
  }

  signedbv_typet difference_type() const
  {
    return signedbv_typet(get_width());
  }

  static void check(
    const typet &type,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    type_with_subtypet::check(type);
    DATA_CHECK(vm, !type.get(ID_width).empty(), "pointer must have width");
  }
};

/// Check whether a reference to a typet is a \ref pointer_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref pointer_typet.
template <>
inline bool can_cast_type<pointer_typet>(const typet &type)
{
  return type.id() == ID_pointer;
}

/// \brief Cast a typet to a \ref pointer_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// pointer_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref pointer_typet.
inline const pointer_typet &to_pointer_type(const typet &type)
{
  PRECONDITION(can_cast_type<pointer_typet>(type));
  pointer_typet::check(type);
  return static_cast<const pointer_typet &>(type);
}

/// \copydoc to_pointer_type(const typet &)
inline pointer_typet &to_pointer_type(typet &type)
{
  PRECONDITION(can_cast_type<pointer_typet>(type));
  pointer_typet::check(type);
  return static_cast<pointer_typet &>(type);
}

/// This method tests,
/// if the given typet is a pointer of type void.
inline bool is_void_pointer(const typet &type)
{
  return type.id() == ID_pointer &&
         to_pointer_type(type).base_type().id() == ID_empty;
}

/// The reference type
///
/// Intends to model C++ reference. Comparing to \ref pointer_typet should
/// never be null.
class reference_typet : public pointer_typet
{
public:
  reference_typet(typet _subtype, std::size_t _width)
    : pointer_typet(std::move(_subtype), _width)
  {
    set(ID_C_reference, true);
  }

  static void check(
    const typet &type,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    PRECONDITION(type.id() == ID_pointer);
    DATA_CHECK(
      vm, type.get_sub().size() == 1, "reference must have one type parameter");
    const reference_typet &reference_type =
      static_cast<const reference_typet &>(type);
    DATA_CHECK(
      vm, !reference_type.get(ID_width).empty(), "reference must have width");
    DATA_CHECK(
      vm, reference_type.get_width() > 0, "reference must have non-zero width");
  }
};

/// Check whether a reference to a typet is a \ref reference_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref reference_typet.
template <>
inline bool can_cast_type<reference_typet>(const typet &type)
{
  return can_cast_type<pointer_typet>(type) && type.get_bool(ID_C_reference);
}

/// \brief Cast a typet to a \ref reference_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// reference_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref reference_typet.
inline const reference_typet &to_reference_type(const typet &type)
{
  PRECONDITION(can_cast_type<reference_typet>(type));
  return static_cast<const reference_typet &>(type);
}

/// \copydoc to_reference_type(const typet &)
inline reference_typet &to_reference_type(typet &type)
{
  PRECONDITION(can_cast_type<reference_typet>(type));
  return static_cast<reference_typet &>(type);
}

bool is_reference(const typet &type);

bool is_rvalue_reference(const typet &type);

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

  static const exprt &root_object(const exprt &expr);
  const exprt &root_object() const
  {
    return root_object(object());
  }

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

  exprt &address()
  {
    return op();
  }

  const exprt &address() const
  {
    return op();
  }
};

template <>
inline bool can_cast_expr<is_dynamic_object_exprt>(const exprt &base)
{
  return base.id() == ID_is_dynamic_object;
}

inline void validate_expr(const is_dynamic_object_exprt &value)
{
  validate_operands(value, 1, "is_dynamic_object must have one operand");
}

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

/// \brief Operator to return the address of an object
class object_address_exprt : public nullary_exprt
{
public:
  explicit object_address_exprt(const symbol_exprt &);

  object_address_exprt(const symbol_exprt &, pointer_typet);

  irep_idt object_identifier() const
  {
    return get(ID_identifier);
  }

  const pointer_typet &type() const
  {
    return static_cast<const pointer_typet &>(exprt::type());
  }

  pointer_typet &type()
  {
    return static_cast<pointer_typet &>(exprt::type());
  }

  /// returns the type of the object whose address is represented
  const typet &object_type() const
  {
    return type().base_type();
  }

  symbol_exprt object_expr() const;
};

template <>
inline bool can_cast_expr<object_address_exprt>(const exprt &base)
{
  return base.id() == ID_object_address;
}

inline void validate_expr(const object_address_exprt &value)
{
  validate_operands(value, 0, "object_address must have zero operands");
}

/// \brief Cast an exprt to an \ref object_address_exprt
///
/// \a expr must be known to be \ref object_address_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref object_address_exprt
inline const object_address_exprt &to_object_address_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_object_address);
  const object_address_exprt &ret =
    static_cast<const object_address_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_object_address_expr(const exprt &)
inline object_address_exprt &to_object_address_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_object_address);
  object_address_exprt &ret = static_cast<object_address_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Operator to return the address of a field relative
/// to a base address
class field_address_exprt : public unary_exprt
{
public:
  /// constructor for field addresses.
  /// The base address must be a pointer to a compound type.
  field_address_exprt(
    exprt base,
    const irep_idt &component_name,
    pointer_typet type);

  exprt &base()
  {
    return op0();
  }

  const exprt &base() const
  {
    return op0();
  }

  const pointer_typet &type() const
  {
    return static_cast<const pointer_typet &>(exprt::type());
  }

  pointer_typet &type()
  {
    return static_cast<pointer_typet &>(exprt::type());
  }

  /// returns the type of the field whose address is represented
  const typet &field_type() const
  {
    return type().base_type();
  }

  const typet &compound_type() const
  {
    return to_pointer_type(base().type()).base_type();
  }

  const irep_idt &component_name() const
  {
    return get(ID_component_name);
  }
};

template <>
inline bool can_cast_expr<field_address_exprt>(const exprt &expr)
{
  return expr.id() == ID_field_address;
}

inline void validate_expr(const field_address_exprt &value)
{
  validate_operands(value, 1, "field_address must have one operand");
}

/// \brief Cast an exprt to an \ref field_address_exprt
///
/// \a expr must be known to be \ref field_address_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref field_address_exprt
inline const field_address_exprt &to_field_address_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_field_address);
  const field_address_exprt &ret =
    static_cast<const field_address_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_field_address_expr(const exprt &)
inline field_address_exprt &to_field_address_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_field_address);
  field_address_exprt &ret = static_cast<field_address_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Operator to return the address of an array element
/// relative to a base address
class element_address_exprt : public binary_exprt
{
public:
  /// constructor for element addresses.
  /// The base address must be a pointer to an element.
  /// The index is expected to have an integer type.
  element_address_exprt(const exprt &base, exprt index);

  const pointer_typet &type() const
  {
    return static_cast<const pointer_typet &>(exprt::type());
  }

  pointer_typet &type()
  {
    return static_cast<pointer_typet &>(exprt::type());
  }

  /// returns the type of the array element whose address is represented
  const typet &element_type() const
  {
    return type().base_type();
  }

  exprt &base()
  {
    return op0();
  }

  const exprt &base() const
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
inline bool can_cast_expr<element_address_exprt>(const exprt &expr)
{
  return expr.id() == ID_element_address;
}

inline void validate_expr(const element_address_exprt &value)
{
  validate_operands(value, 2, "element_address must have two operands");
}

/// \brief Cast an exprt to an \ref element_address_exprt
///
/// \a expr must be known to be \ref element_address_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref element_address_exprt
inline const element_address_exprt &to_element_address_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_element_address);
  const element_address_exprt &ret =
    static_cast<const element_address_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_element_address_expr(const exprt &)
inline element_address_exprt &to_element_address_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_element_address);
  element_address_exprt &ret = static_cast<element_address_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Operator to dereference a pointer
class dereference_exprt : public unary_exprt
{
public:
  // The given operand must have pointer type.
  explicit dereference_exprt(const exprt &op)
    : unary_exprt(ID_dereference, op, to_pointer_type(op.type()).base_type())
  {
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

/// \brief The null pointer constant
class null_pointer_exprt : public constant_exprt
{
public:
  explicit null_pointer_exprt(pointer_typet type)
    : constant_exprt(ID_NULL, std::move(type))
  {
  }
};

/// \brief A base class for a predicate that indicates that an
/// address range is ok to read or write or both
class r_or_w_ok_exprt : public binary_predicate_exprt
{
public:
  explicit r_or_w_ok_exprt(irep_idt id, exprt pointer, exprt size)
    : binary_predicate_exprt(std::move(pointer), id, std::move(size))
  {
  }

  const exprt &pointer() const
  {
    return op0();
  }

  const exprt &size() const
  {
    return op1();
  }
};

inline const r_or_w_ok_exprt &to_r_or_w_ok_expr(const exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_r_ok || expr.id() == ID_w_ok || expr.id() == ID_rw_ok);
  auto &ret = static_cast<const r_or_w_ok_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief A predicate that indicates that an address range is ok to read
class r_ok_exprt : public r_or_w_ok_exprt
{
public:
  explicit r_ok_exprt(exprt pointer, exprt size)
    : r_or_w_ok_exprt(ID_r_ok, std::move(pointer), std::move(size))
  {
  }
};

inline const r_ok_exprt &to_r_ok_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_r_ok);
  const r_ok_exprt &ret = static_cast<const r_ok_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief A predicate that indicates that an address range is ok to write
class w_ok_exprt : public r_or_w_ok_exprt
{
public:
  explicit w_ok_exprt(exprt pointer, exprt size)
    : r_or_w_ok_exprt(ID_w_ok, std::move(pointer), std::move(size))
  {
  }
};

inline const w_ok_exprt &to_w_ok_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_w_ok);
  const w_ok_exprt &ret = static_cast<const w_ok_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief Pointer-typed bitvector constant annotated with the pointer
/// expression that the bitvector is the numeric representation of.
/// This variation of a constant expression is only used in the context of a
/// GOTO trace, to give both the numeric value and the symbolic value of a
/// pointer, e.g. numeric value "0xabcd0004" but symbolic value
/// "&some_object + 4". The numeric value is stored in the usual value slot and
/// the symbolic value is accessed using the `symbolic_pointer` method
/// introduced by this class.
class annotated_pointer_constant_exprt : public unary_exprt
{
public:
  annotated_pointer_constant_exprt(
    const irep_idt &_value,
    const exprt &_pointer)
    : unary_exprt(ID_annotated_pointer_constant, _pointer, _pointer.type())
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

  exprt &symbolic_pointer()
  {
    return op0();
  }

  const exprt &symbolic_pointer() const
  {
    return op0();
  }
};

template <>
inline bool can_cast_expr<annotated_pointer_constant_exprt>(const exprt &base)
{
  return base.id() == ID_annotated_pointer_constant;
}

inline void validate_expr(const annotated_pointer_constant_exprt &value)
{
  validate_operands(
    value, 1, "Annotated pointer constant must have one operand");
}

/// \brief Cast an exprt to an \ref annotated_pointer_constant_exprt
///
/// \a expr must be known to be \ref annotated_pointer_constant_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref annotated_pointer_constant_exprt
inline const annotated_pointer_constant_exprt &
to_annotated_pointer_constant_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_annotated_pointer_constant);
  const annotated_pointer_constant_exprt &ret =
    static_cast<const annotated_pointer_constant_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_annotated_pointer_constant_expr(const exprt &)
inline annotated_pointer_constant_exprt &
to_annotated_pointer_constant_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_annotated_pointer_constant);
  annotated_pointer_constant_exprt &ret =
    static_cast<annotated_pointer_constant_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// The offset (in bytes) of a pointer relative to the object
class pointer_offset_exprt : public unary_exprt
{
public:
  explicit pointer_offset_exprt(exprt pointer, typet type)
    : unary_exprt(ID_pointer_offset, std::move(pointer), std::move(type))
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

template <>
inline bool can_cast_expr<pointer_offset_exprt>(const exprt &base)
{
  return base.id() == ID_pointer_offset;
}

inline void validate_expr(const pointer_offset_exprt &value)
{
  validate_operands(value, 1, "pointer_offset must have one operand");
  DATA_INVARIANT(
    value.pointer().type().id() == ID_pointer,
    "pointer_offset must have pointer-typed operand");
}

/// \brief Cast an exprt to a \ref pointer_offset_exprt
///
/// \a expr must be known to be \ref pointer_offset_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref pointer_offset_exprt
inline const pointer_offset_exprt &to_pointer_offset_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_pointer_offset);
  const pointer_offset_exprt &ret =
    static_cast<const pointer_offset_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_pointer_offset_expr(const exprt &)
inline pointer_offset_exprt &to_pointer_offset_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_pointer_offset);
  pointer_offset_exprt &ret = static_cast<pointer_offset_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// A numerical identifier for the object a pointer points to
class pointer_object_exprt : public unary_exprt
{
public:
  explicit pointer_object_exprt(exprt pointer, typet type)
    : unary_exprt(ID_pointer_object, std::move(pointer), std::move(type))
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

template <>
inline bool can_cast_expr<pointer_object_exprt>(const exprt &base)
{
  return base.id() == ID_pointer_object;
}

inline void validate_expr(const pointer_object_exprt &value)
{
  validate_operands(value, 1, "pointer_object must have one operand");
  DATA_INVARIANT(
    value.pointer().type().id() == ID_pointer,
    "pointer_object must have pointer-typed operand");
}

/// \brief Cast an exprt to a \ref pointer_object_exprt
///
/// \a expr must be known to be \ref pointer_object_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref pointer_object_exprt
inline const pointer_object_exprt &to_pointer_object_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_pointer_object);
  const pointer_object_exprt &ret =
    static_cast<const pointer_object_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_pointer_object_expr(const exprt &)
inline pointer_object_exprt &to_pointer_object_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_pointer_object);
  pointer_object_exprt &ret = static_cast<pointer_object_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// Expression for finding the size (in bytes) of the object a pointer points
/// to.
class object_size_exprt : public unary_exprt
{
public:
  explicit object_size_exprt(exprt pointer, typet type)
    : unary_exprt(ID_object_size, std::move(pointer), std::move(type))
  {
  }

  exprt &pointer()
  {
    return op();
  }

  const exprt &pointer() const
  {
    return op();
  }
};

/// \brief Cast an exprt to a \ref object_size_exprt
///
/// \a expr must be known to be \ref object_size_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref object_size_exprt
inline const object_size_exprt &to_object_size_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_object_size);
  const object_size_exprt &ret = static_cast<const object_size_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_object_size_expr(const exprt &)
inline object_size_exprt &to_object_size_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_object_size);
  object_size_exprt &ret = static_cast<object_size_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

template <>
inline bool can_cast_expr<object_size_exprt>(const exprt &base)
{
  return base.id() == ID_object_size;
}

inline void validate_expr(const object_size_exprt &value)
{
  validate_operands(value, 1, "Object size expression must have one operand.");
  DATA_INVARIANT(
    can_cast_type<pointer_typet>(value.pointer().type()),
    "Object size expression must have pointer typed operand.");
}

/// A predicate that indicates that a zero-terminated string
/// starts at the given address.
/// This is an experimental feature for CHC encodings -- do not use.
class is_cstring_exprt : public unary_predicate_exprt
{
public:
  explicit is_cstring_exprt(exprt address)
    : unary_predicate_exprt(ID_is_cstring, std::move(address))
  {
    PRECONDITION(as_const(*this).address().type().id() == ID_pointer);
  }

  exprt &address()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op0();
  }
};

template <>
inline bool can_cast_expr<is_cstring_exprt>(const exprt &base)
{
  return base.id() == ID_is_cstring;
}

inline void validate_expr(const is_cstring_exprt &value)
{
  validate_operands(value, 1, "is_cstring must have one operand");
}

/// \brief Cast an exprt to a \ref is_cstring_exprt
///
/// \a expr must be known to be \ref is_cstring_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref is_cstring_exprt
inline const is_cstring_exprt &to_is_cstring_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_is_cstring);
  const is_cstring_exprt &ret = static_cast<const is_cstring_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_is_cstring_expr(const exprt &)
inline is_cstring_exprt &to_is_cstring_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_is_cstring);
  is_cstring_exprt &ret = static_cast<is_cstring_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// An expression, akin to ISO C's strlen, that denotes the
/// length of a zero-terminated string that starts at the
/// given address. The trailing zero is not included in the count.
/// This is an experimental feature for CHC encodings -- do not use.
class cstrlen_exprt : public unary_exprt
{
public:
  cstrlen_exprt(exprt address, typet type)
    : unary_exprt(ID_cstrlen, std::move(address), std::move(type))
  {
    PRECONDITION(as_const(*this).address().type().id() == ID_pointer);
  }

  exprt &address()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op0();
  }
};

template <>
inline bool can_cast_expr<cstrlen_exprt>(const exprt &base)
{
  return base.id() == ID_cstrlen;
}

inline void validate_expr(const cstrlen_exprt &value)
{
  validate_operands(value, 1, "cstrlen must have one operand");
}

/// \brief Cast an exprt to a \ref cstrlen_exprt
///
/// \a expr must be known to be \ref cstrlen_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref cstrlen_exprt
inline const cstrlen_exprt &to_cstrlen_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_cstrlen);
  const cstrlen_exprt &ret = static_cast<const cstrlen_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_cstrlen_expr(const exprt &)
inline cstrlen_exprt &to_cstrlen_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_cstrlen);
  cstrlen_exprt &ret = static_cast<cstrlen_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// A predicate that indicates that the object pointed to is live.
/// This is an experimental feature for CHC encodings -- do not use.
class live_object_exprt : public unary_predicate_exprt
{
public:
  explicit live_object_exprt(exprt pointer)
    : unary_predicate_exprt(ID_live_object, std::move(pointer))
  {
    PRECONDITION(as_const(*this).pointer().type().id() == ID_pointer);
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

template <>
inline bool can_cast_expr<live_object_exprt>(const exprt &base)
{
  return base.id() == ID_live_object;
}

inline void validate_expr(const live_object_exprt &value)
{
  validate_operands(value, 1, "live_object must have one operand");
}

/// \brief Cast an exprt to a \ref live_object_exprt
///
/// \a expr must be known to be \ref live_object_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref live_object_exprt
inline const live_object_exprt &to_live_object_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_live_object);
  const live_object_exprt &ret = static_cast<const live_object_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_live_object_expr(const exprt &)
inline live_object_exprt &to_live_object_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_live_object);
  live_object_exprt &ret = static_cast<live_object_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// A predicate that indicates that the object pointed to is writeable.
/// This is an experimental feature for CHC encodings -- do not use.
class writeable_object_exprt : public unary_predicate_exprt
{
public:
  explicit writeable_object_exprt(exprt pointer)
    : unary_predicate_exprt(ID_writeable_object, std::move(pointer))
  {
    PRECONDITION(as_const(*this).pointer().type().id() == ID_pointer);
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

template <>
inline bool can_cast_expr<writeable_object_exprt>(const exprt &base)
{
  return base.id() == ID_writeable_object;
}

inline void validate_expr(const writeable_object_exprt &value)
{
  validate_operands(value, 1, "writeable_object must have one operand");
}

/// \brief Cast an exprt to a \ref writeable_object_exprt
///
/// \a expr must be known to be \ref writeable_object_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref writeable_object_exprt
inline const writeable_object_exprt &to_writeable_object_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_writeable_object);
  const writeable_object_exprt &ret =
    static_cast<const writeable_object_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_writeable_object_expr(const exprt &)
inline writeable_object_exprt &to_writeable_object_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_writeable_object);
  writeable_object_exprt &ret = static_cast<writeable_object_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

#endif // CPROVER_UTIL_POINTER_EXPR_H
