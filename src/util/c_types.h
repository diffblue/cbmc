/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_C_TYPES_H
#define CPROVER_UTIL_C_TYPES_H

#include "deprecate.h"
#include "pointer_expr.h"

/// Type for C bit fields
/// These are both 'bitvector_typet' (they have a width)
/// and 'type_with_subtypet' (they have a subtype)
class c_bit_field_typet : public bitvector_typet
{
public:
  explicit c_bit_field_typet(typet _subtype, std::size_t width)
    : bitvector_typet(ID_c_bit_field, width)
  {
    subtype().swap(_subtype);
  }

  // These have a sub-type. The preferred way to access it
  // are the underlying_type methods.
  const typet &underlying_type() const
  {
    return subtype();
  }

  typet &underlying_type()
  {
    return subtype();
  }
};

/// Check whether a reference to a typet is a \ref c_bit_field_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref c_bit_field_typet.
template <>
inline bool can_cast_type<c_bit_field_typet>(const typet &type)
{
  return type.id() == ID_c_bit_field;
}

/// \brief Cast a typet to a \ref c_bit_field_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// c_bit_field_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref c_bit_field_typet.
inline const c_bit_field_typet &to_c_bit_field_type(const typet &type)
{
  PRECONDITION(can_cast_type<c_bit_field_typet>(type));
  return static_cast<const c_bit_field_typet &>(type);
}

/// \copydoc to_c_bit_field_type(const typet &type)
inline c_bit_field_typet &to_c_bit_field_type(typet &type)
{
  PRECONDITION(can_cast_type<c_bit_field_typet>(type));
  return static_cast<c_bit_field_typet &>(type);
}

/// The C/C++ Booleans
class c_bool_typet : public bitvector_typet
{
public:
  explicit c_bool_typet(std::size_t width) : bitvector_typet(ID_c_bool, width)
  {
  }

  static void check(
    const typet &type,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(vm, !type.get(ID_width).empty(), "C bool type must have width");
  }
};

/// Check whether a reference to a typet is a \ref c_bool_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref c_bool_typet.
template <>
inline bool can_cast_type<c_bool_typet>(const typet &type)
{
  return type.id() == ID_c_bool;
}

/// \brief Cast a typet to a \ref c_bool_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// c_bool_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref c_bool_typet.
inline const c_bool_typet &to_c_bool_type(const typet &type)
{
  PRECONDITION(can_cast_type<c_bool_typet>(type));
  c_bool_typet::check(type);
  return static_cast<const c_bool_typet &>(type);
}

/// \copydoc to_c_bool_type(const typet &)
inline c_bool_typet &to_c_bool_type(typet &type)
{
  PRECONDITION(can_cast_type<c_bool_typet>(type));
  c_bool_typet::check(type);
  return static_cast<c_bool_typet &>(type);
}

/// The union type
///
/// For example, C union.
class union_typet : public struct_union_typet
{
public:
  union_typet() : struct_union_typet(ID_union)
  {
  }

  explicit union_typet(componentst _components)
    : struct_union_typet(ID_union, std::move(_components))
  {
  }

  /// Determine the member of maximum bit width in a union type. If no member,
  /// or a member of non-fixed width can be found, return nullopt.
  /// \param ns: Namespace to resolve tag types.
  /// \return Pair of a componentt pointing to the maximum fixed bit-width
  ///   member of the union type and the bit width of that member.
  optionalt<std::pair<struct_union_typet::componentt, mp_integer>>
  find_widest_union_component(const namespacet &ns) const;
};

/// Check whether a reference to a typet is a \ref union_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref union_typet.
template <>
inline bool can_cast_type<union_typet>(const typet &type)
{
  return type.id() == ID_union;
}

/// \brief Cast a typet to a \ref union_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// union_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref union_typet
inline const union_typet &to_union_type(const typet &type)
{
  PRECONDITION(can_cast_type<union_typet>(type));
  return static_cast<const union_typet &>(type);
}

/// \copydoc to_union_type(const typet &)
inline union_typet &to_union_type(typet &type)
{
  PRECONDITION(can_cast_type<union_typet>(type));
  return static_cast<union_typet &>(type);
}

/// A union tag type, i.e., \ref union_typet with an identifier
class union_tag_typet : public tag_typet
{
public:
  explicit union_tag_typet(const irep_idt &identifier)
    : tag_typet(ID_union_tag, identifier)
  {
  }
};

/// Check whether a reference to a typet is a \ref union_tag_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref union_tag_typet.
template <>
inline bool can_cast_type<union_tag_typet>(const typet &type)
{
  return type.id() == ID_union_tag;
}

/// \brief Cast a typet to a \ref union_tag_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// union_tag_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref union_tag_typet.
inline const union_tag_typet &to_union_tag_type(const typet &type)
{
  PRECONDITION(can_cast_type<union_tag_typet>(type));
  return static_cast<const union_tag_typet &>(type);
}

/// \copydoc to_union_tag_type(const typet &)
inline union_tag_typet &to_union_tag_type(typet &type)
{
  PRECONDITION(can_cast_type<union_tag_typet>(type));
  return static_cast<union_tag_typet &>(type);
}

/// The type of C enums
class c_enum_typet : public type_with_subtypet
{
public:
  explicit c_enum_typet(typet _subtype)
    : type_with_subtypet(ID_c_enum, std::move(_subtype))
  {
  }

  class c_enum_membert : public irept
  {
  public:
    irep_idt get_value() const
    {
      return get(ID_value);
    }
    void set_value(const irep_idt &value)
    {
      set(ID_value, value);
    }
    irep_idt get_identifier() const
    {
      return get(ID_identifier);
    }
    void set_identifier(const irep_idt &identifier)
    {
      set(ID_identifier, identifier);
    }
    irep_idt get_base_name() const
    {
      return get(ID_base_name);
    }
    void set_base_name(const irep_idt &base_name)
    {
      set(ID_base_name, base_name);
    }
  };

  typedef std::vector<c_enum_membert> memberst;

  const memberst &members() const
  {
    return (const memberst &)(find(ID_body).get_sub());
  }

  /// enum types may be incomplete
  bool is_incomplete() const
  {
    return get_bool(ID_incomplete);
  }

  /// enum types may be incomplete
  void make_incomplete()
  {
    set(ID_incomplete, true);
  }

  // The preferred way to access the subtype
  // are the underlying_type methods.
  const typet &underlying_type() const
  {
    return subtype();
  }

  typet &underlying_type()
  {
    return subtype();
  }
};

/// Check whether a reference to a typet is a \ref c_enum_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref c_enum_typet.
template <>
inline bool can_cast_type<c_enum_typet>(const typet &type)
{
  return type.id() == ID_c_enum;
}

/// \brief Cast a typet to a \ref c_enum_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// c_enum_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref c_enum_typet.
inline const c_enum_typet &to_c_enum_type(const typet &type)
{
  PRECONDITION(can_cast_type<c_enum_typet>(type));
  return static_cast<const c_enum_typet &>(type);
}

/// \copydoc to_c_enum_type(const typet &)
inline c_enum_typet &to_c_enum_type(typet &type)
{
  PRECONDITION(can_cast_type<c_enum_typet>(type));
  return static_cast<c_enum_typet &>(type);
}

/// C enum tag type, i.e., \ref c_enum_typet with an identifier
class c_enum_tag_typet : public tag_typet
{
public:
  explicit c_enum_tag_typet(const irep_idt &identifier)
    : tag_typet(ID_c_enum_tag, identifier)
  {
  }
};

/// Check whether a reference to a typet is a \ref c_enum_tag_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref c_enum_tag_typet.
template <>
inline bool can_cast_type<c_enum_tag_typet>(const typet &type)
{
  return type.id() == ID_c_enum_tag;
}

/// \brief Cast a typet to a \ref c_enum_tag_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// c_enum_tag_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref c_enum_tag_typet.
inline const c_enum_tag_typet &to_c_enum_tag_type(const typet &type)
{
  PRECONDITION(can_cast_type<c_enum_tag_typet>(type));
  return static_cast<const c_enum_tag_typet &>(type);
}

/// \copydoc to_c_enum_tag_type(const typet &)
inline c_enum_tag_typet &to_c_enum_tag_type(typet &type)
{
  PRECONDITION(can_cast_type<c_enum_tag_typet>(type));
  return static_cast<c_enum_tag_typet &>(type);
}

class code_with_contract_typet : public code_typet
{
public:
  /// Constructs a new 'code with contract' type, i.e., a function type
  /// decorated with a function contract.
  /// \param _parameters: The vector of function parameters.
  /// \param _return_type: The return type.
  code_with_contract_typet(parameterst _parameters, typet _return_type)
    : code_typet(std::move(_parameters), std::move(_return_type))
  {
  }

  const exprt::operandst &assigns() const
  {
    return static_cast<const exprt &>(find(ID_C_spec_assigns)).operands();
  }

  exprt::operandst &assigns()
  {
    return static_cast<exprt &>(add(ID_C_spec_assigns)).operands();
  }

  const exprt::operandst &requires() const
  {
    return static_cast<const exprt &>(find(ID_C_spec_requires)).operands();
  }

  exprt::operandst &requires()
  {
    return static_cast<exprt &>(add(ID_C_spec_requires)).operands();
  }

  const exprt::operandst &ensures() const
  {
    return static_cast<const exprt &>(find(ID_C_spec_ensures)).operands();
  }

  exprt::operandst &ensures()
  {
    return static_cast<exprt &>(add(ID_C_spec_ensures)).operands();
  }
};

/// Check whether a reference to a typet is a \ref code_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref code_typet.
template <>
inline bool can_cast_type<code_with_contract_typet>(const typet &type)
{
  return type.id() == ID_code;
}

/// \brief Cast a typet to a \ref code_with_contract_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// code_with_contract_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref code_with_contract_typet.
inline const code_with_contract_typet &
to_code_with_contract_type(const typet &type)
{
  PRECONDITION(can_cast_type<code_with_contract_typet>(type));
  code_with_contract_typet::check(type);
  return static_cast<const code_with_contract_typet &>(type);
}

/// \copydoc to_code_type(const typet &)
inline code_with_contract_typet &to_code_with_contract_type(typet &type)
{
  PRECONDITION(can_cast_type<code_with_contract_typet>(type));
  code_with_contract_typet::check(type);
  return static_cast<code_with_contract_typet &>(type);
}

DEPRECATED(
  SINCE(2022, 1, 13, "use c_index_type() or array_typet::index_type() instead"))
bitvector_typet index_type();

DEPRECATED(SINCE(2022, 1, 13, "use c_enum_constant_type() instead"))
bitvector_typet enum_constant_type();

bitvector_typet c_enum_constant_type();
bitvector_typet c_index_type();
signedbv_typet signed_int_type();
unsignedbv_typet unsigned_int_type();
signedbv_typet signed_long_int_type();
signedbv_typet signed_short_int_type();
unsignedbv_typet unsigned_short_int_type();
signedbv_typet signed_long_long_int_type();
unsignedbv_typet unsigned_long_int_type();
unsignedbv_typet unsigned_long_long_int_type();
typet c_bool_type();
bitvector_typet char_type();
unsignedbv_typet unsigned_char_type();
signedbv_typet signed_char_type();
bitvector_typet wchar_t_type();
unsignedbv_typet char16_t_type();
unsignedbv_typet char32_t_type();
floatbv_typet float_type();
floatbv_typet double_type();
floatbv_typet long_double_type();
unsignedbv_typet size_type();
signedbv_typet signed_size_type();
signedbv_typet pointer_diff_type();
pointer_typet pointer_type(const typet &);
empty_typet void_type();

// This is for Java and C++
reference_typet reference_type(const typet &);

// Turns an ID_C_c_type into a string, e.g.,
// ID_signed_int gets "signed int".
std::string c_type_as_string(const irep_idt &);

#endif // CPROVER_UTIL_C_TYPES_H
