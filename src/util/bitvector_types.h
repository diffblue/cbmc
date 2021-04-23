/*******************************************************************\

Module: Pre-defined bitvector types

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pre-defined bitvector types

#ifndef CPROVER_UTIL_BITVECTOR_TYPES_H
#define CPROVER_UTIL_BITVECTOR_TYPES_H

#include "std_types.h"

/// This method tests,
/// if the given typet is a signed or unsigned bitvector.
inline bool is_signed_or_unsigned_bitvector(const typet &type)
{
  return type.id() == ID_signedbv || type.id() == ID_unsignedbv;
}

/// \brief Cast a typet to a \ref bitvector_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// bitvector_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref bitvector_typet.
inline const bitvector_typet &to_bitvector_type(const typet &type)
{
  PRECONDITION(can_cast_type<bitvector_typet>(type));

  return static_cast<const bitvector_typet &>(type);
}

/// \copydoc to_bitvector_type(const typet &type)
inline bitvector_typet &to_bitvector_type(typet &type)
{
  PRECONDITION(can_cast_type<bitvector_typet>(type));

  return static_cast<bitvector_typet &>(type);
}

/// Fixed-width bit-vector without numerical interpretation
class bv_typet : public bitvector_typet
{
public:
  explicit bv_typet(std::size_t width) : bitvector_typet(ID_bv)
  {
    set_width(width);
  }

  static void check(
    const typet &type,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm, !type.get(ID_width).empty(), "bitvector type must have width");
  }
};

/// Check whether a reference to a typet is a \ref bv_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref bv_typet.
template <>
inline bool can_cast_type<bv_typet>(const typet &type)
{
  return type.id() == ID_bv;
}

/// \brief Cast a typet to a \ref bv_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// bv_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref bv_typet.
inline const bv_typet &to_bv_type(const typet &type)
{
  PRECONDITION(can_cast_type<bv_typet>(type));
  bv_typet::check(type);
  return static_cast<const bv_typet &>(type);
}

/// \copydoc to_bv_type(const typet &)
inline bv_typet &to_bv_type(typet &type)
{
  PRECONDITION(can_cast_type<bv_typet>(type));
  bv_typet::check(type);
  return static_cast<bv_typet &>(type);
}

/// Fixed-width bit-vector representing a signed or unsigned integer
class integer_bitvector_typet : public bitvector_typet
{
public:
  integer_bitvector_typet(const irep_idt &id, std::size_t width)
    : bitvector_typet(id, width)
  {
  }

  /// Return the smallest value that can be represented using this type.
  mp_integer smallest() const;
  /// Return the largest value that can be represented using this type.
  mp_integer largest() const;

  // If we ever need any of the following three methods in \ref fixedbv_typet or
  // \ref floatbv_typet, we might want to move them to a new class
  // numeric_bitvector_typet, which would be between integer_bitvector_typet and
  // bitvector_typet in the hierarchy.

  /// Return an expression representing the smallest value of this type.
  constant_exprt smallest_expr() const;
  /// Return an expression representing the zero value of this type.
  constant_exprt zero_expr() const;
  /// Return an expression representing the largest value of this type.
  constant_exprt largest_expr() const;
};

/// Check whether a reference to a typet is an \ref integer_bitvector_typet.
/// \param type: Source type.
/// \return True if \p type is an \ref integer_bitvector_typet.
template <>
inline bool can_cast_type<integer_bitvector_typet>(const typet &type)
{
  return type.id() == ID_signedbv || type.id() == ID_unsignedbv;
}

/// \brief Cast a typet to an \ref integer_bitvector_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// integer_bitvector_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref integer_bitvector_typet.
inline const integer_bitvector_typet &
to_integer_bitvector_type(const typet &type)
{
  PRECONDITION(can_cast_type<integer_bitvector_typet>(type));

  return static_cast<const integer_bitvector_typet &>(type);
}

/// \copydoc to_integer_bitvector_type(const typet &type)
inline integer_bitvector_typet &to_integer_bitvector_type(typet &type)
{
  PRECONDITION(can_cast_type<integer_bitvector_typet>(type));

  return static_cast<integer_bitvector_typet &>(type);
}

/// Fixed-width bit-vector with unsigned binary interpretation
class unsignedbv_typet : public integer_bitvector_typet
{
public:
  explicit unsignedbv_typet(std::size_t width)
    : integer_bitvector_typet(ID_unsignedbv, width)
  {
  }

  static void check(
    const typet &type,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    bitvector_typet::check(type, vm);
  }
};

/// Check whether a reference to a typet is a \ref unsignedbv_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref unsignedbv_typet.
template <>
inline bool can_cast_type<unsignedbv_typet>(const typet &type)
{
  return type.id() == ID_unsignedbv;
}

/// \brief Cast a typet to an \ref unsignedbv_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// unsignedbv_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref unsignedbv_typet.
inline const unsignedbv_typet &to_unsignedbv_type(const typet &type)
{
  PRECONDITION(can_cast_type<unsignedbv_typet>(type));
  unsignedbv_typet::check(type);
  return static_cast<const unsignedbv_typet &>(type);
}

/// \copydoc to_unsignedbv_type(const typet &)
inline unsignedbv_typet &to_unsignedbv_type(typet &type)
{
  PRECONDITION(can_cast_type<unsignedbv_typet>(type));
  unsignedbv_typet::check(type);
  return static_cast<unsignedbv_typet &>(type);
}

/// Fixed-width bit-vector with two's complement interpretation
class signedbv_typet : public integer_bitvector_typet
{
public:
  explicit signedbv_typet(std::size_t width)
    : integer_bitvector_typet(ID_signedbv, width)
  {
  }

  static void check(
    const typet &type,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm, !type.get(ID_width).empty(), "signed bitvector type must have width");
  }
};

/// Check whether a reference to a typet is a \ref signedbv_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref signedbv_typet.
template <>
inline bool can_cast_type<signedbv_typet>(const typet &type)
{
  return type.id() == ID_signedbv;
}

/// \brief Cast a typet to a \ref signedbv_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// signedbv_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref signedbv_typet.
inline const signedbv_typet &to_signedbv_type(const typet &type)
{
  PRECONDITION(can_cast_type<signedbv_typet>(type));
  signedbv_typet::check(type);
  return static_cast<const signedbv_typet &>(type);
}

/// \copydoc to_signedbv_type(const typet &)
inline signedbv_typet &to_signedbv_type(typet &type)
{
  PRECONDITION(can_cast_type<signedbv_typet>(type));
  signedbv_typet::check(type);
  return static_cast<signedbv_typet &>(type);
}

/// Fixed-width bit-vector with signed fixed-point interpretation
///
/// Integer and fraction bits refer to the number of bits before and after
/// the decimal point, respectively. The width is the sum of the two.
class fixedbv_typet : public bitvector_typet
{
public:
  fixedbv_typet() : bitvector_typet(ID_fixedbv)
  {
  }

  std::size_t get_fraction_bits() const
  {
    return get_width() - get_integer_bits();
  }

  std::size_t get_integer_bits() const;

  void set_integer_bits(std::size_t b)
  {
    set_size_t(ID_integer_bits, b);
  }

  static void check(
    const typet &type,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm, !type.get(ID_width).empty(), "fixed bitvector type must have width");
  }
};

/// Check whether a reference to a typet is a \ref fixedbv_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref fixedbv_typet.
template <>
inline bool can_cast_type<fixedbv_typet>(const typet &type)
{
  return type.id() == ID_fixedbv;
}

/// \brief Cast a typet to a \ref fixedbv_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// fixedbv_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref fixedbv_typet.
inline const fixedbv_typet &to_fixedbv_type(const typet &type)
{
  PRECONDITION(can_cast_type<fixedbv_typet>(type));
  fixedbv_typet::check(type);
  return static_cast<const fixedbv_typet &>(type);
}

/// \copydoc to_fixedbv_type(const typet &)
inline fixedbv_typet &to_fixedbv_type(typet &type)
{
  PRECONDITION(can_cast_type<fixedbv_typet>(type));
  fixedbv_typet::check(type);
  return static_cast<fixedbv_typet &>(type);
}

/// Fixed-width bit-vector with IEEE floating-point interpretation
class floatbv_typet : public bitvector_typet
{
public:
  floatbv_typet() : bitvector_typet(ID_floatbv)
  {
  }

  std::size_t get_e() const
  {
    // subtract one for sign bit
    return get_width() - get_f() - 1;
  }

  std::size_t get_f() const;

  void set_f(std::size_t b)
  {
    set_size_t(ID_f, b);
  }

  static void check(
    const typet &type,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm, !type.get(ID_width).empty(), "float bitvector type must have width");
  }
};

/// Check whether a reference to a typet is a \ref floatbv_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref floatbv_typet.
template <>
inline bool can_cast_type<floatbv_typet>(const typet &type)
{
  return type.id() == ID_floatbv;
}

/// \brief Cast a typet to a \ref floatbv_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// floatbv_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref floatbv_typet.
inline const floatbv_typet &to_floatbv_type(const typet &type)
{
  PRECONDITION(can_cast_type<floatbv_typet>(type));
  floatbv_typet::check(type);
  return static_cast<const floatbv_typet &>(type);
}

/// \copydoc to_floatbv_type(const typet &)
inline floatbv_typet &to_floatbv_type(typet &type)
{
  PRECONDITION(can_cast_type<floatbv_typet>(type));
  floatbv_typet::check(type);
  return static_cast<floatbv_typet &>(type);
}

#endif // CPROVER_UTIL_BITVECTOR_TYPES_H
