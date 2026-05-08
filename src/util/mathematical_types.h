/*******************************************************************\

Module: Mathematical types

Author: Daniel Kroening, kroening@kroening.com
        Maria Svorenova, maria.svorenova@diffblue.com

\*******************************************************************/

/// \file
/// Mathematical types

#ifndef CPROVER_UTIL_MATHEMATICAL_TYPES_H
#define CPROVER_UTIL_MATHEMATICAL_TYPES_H

#include "expr_cast.h" // IWYU pragma: keep
#include "invariant.h"
#include "mp_arith.h"
#include "type.h"

class constant_exprt;

/// Unbounded, signed integers (mathematical integers, not bitvectors)
class integer_typet : public typet
{
public:
  integer_typet() : typet(ID_integer)
  {
  }

  constant_exprt zero_expr() const;
  constant_exprt one_expr() const;
};

/// Natural numbers including zero (mathematical integers, not bitvectors)
class natural_typet : public typet
{
public:
  natural_typet() : typet(ID_natural)
  {
  }

  constant_exprt zero_expr() const;
  constant_exprt one_expr() const;
};

/// Unbounded, signed rational numbers
class rational_typet : public typet
{
public:
  rational_typet() : typet(ID_rational)
  {
  }

  constant_exprt zero_expr() const;
  constant_exprt one_expr() const;
};

/// Unbounded, signed real numbers
class real_typet : public typet
{
public:
  real_typet() : typet(ID_real)
  {
  }

  constant_exprt zero_expr() const;
  constant_exprt one_expr() const;
};

/// A type for mathematical functions (do not confuse with functions/methods
/// in code)
class mathematical_function_typet : public type_with_subtypest
{
public:
  // the domain of the function is composed of zero, one, or
  // many variables, given by their type
  using domaint = std::vector<typet>;

  mathematical_function_typet(const domaint &_domain, const typet &_codomain)
    : type_with_subtypest(
        ID_mathematical_function,
        {type_with_subtypest(irep_idt(), _domain), _codomain})
  {
  }

  domaint &domain()
  {
    return (domaint &)to_type_with_subtypes(subtypes()[0]).subtypes();
  }

  const domaint &domain() const
  {
    return (const domaint &)to_type_with_subtypes(subtypes()[0]).subtypes();
  }

  void add_variable(const typet &_type)
  {
    domain().push_back(_type);
  }

  /// Return the codomain, i.e., the set of values that the function maps to
  /// (the "target").
  typet &codomain()
  {
    return subtypes()[1];
  }

  /// \copydoc codomain()
  const typet &codomain() const
  {
    return subtypes()[1];
  }
};

/// Check whether a reference to a typet is a \ref mathematical_function_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref mathematical_function_typet.
template <>
inline bool can_cast_type<mathematical_function_typet>(const typet &type)
{
  return type.id() == ID_mathematical_function;
}

/// \brief Cast a typet to a \ref mathematical_function_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// mathematical_function_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref mathematical_function_typet.
inline const mathematical_function_typet &
to_mathematical_function_type(const typet &type)
{
  PRECONDITION(can_cast_type<mathematical_function_typet>(type));
  return static_cast<const mathematical_function_typet &>(type);
}

/// \copydoc to_mathematical_function_type(const typet &)
inline mathematical_function_typet &to_mathematical_function_type(typet &type)
{
  PRECONDITION(can_cast_type<mathematical_function_typet>(type));
  return static_cast<mathematical_function_typet &>(type);
}

/// A type for closed integer intervals `[from, to]`. Both endpoints are
/// inclusive. The interval may be empty (if `from > to`).
class integer_range_typet : public typet
{
public:
  integer_range_typet(const mp_integer &_from, const mp_integer &_to)
    : typet(ID_range)
  {
    from(_from);
    to(_to);
  }

  /// \return The lower bound of the interval (inclusive).
  mp_integer from() const;

  /// \return The upper bound of the interval (inclusive).
  mp_integer to() const;

  /// \return True iff the given value lies within the closed interval
  ///   `[from(), to()]`.
  bool includes(const mp_integer &) const;

  /// \return A constant expression of this type representing the value 0.
  /// \remark Precondition: the interval must include 0, i.e.
  ///   `includes(0)` must hold.
  constant_exprt zero_expr() const;

  /// \return A constant expression of this type representing the value 1.
  /// \remark Precondition: the interval must include 1, i.e.
  ///   `includes(1)` must hold.
  constant_exprt one_expr() const;

  /// \return The number of integers in the closed interval `[from(), to()]`,
  ///   or `0` if the range is empty (i.e. `from() > to()`).
  mp_integer size() const;

  /// \return True iff the range contains no elements, i.e. `from() > to()`
  ///   (equivalently, `size() == 0`).
  bool empty() const;

  void from(const mp_integer &);
  void to(const mp_integer &);
};

/// Check whether a reference to a typet is a \ref integer_range_typet.
/// \param type: Source type.
/// \return True if \p type is a \ref integer_range_typet.
template <>
inline bool can_cast_type<integer_range_typet>(const typet &type)
{
  return type.id() == ID_range;
}

/// \brief Cast a typet to a \ref integer_range_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// integer_range_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref integer_range_typet.
inline const integer_range_typet &to_integer_range_type(const typet &type)
{
  PRECONDITION(can_cast_type<integer_range_typet>(type));
  return static_cast<const integer_range_typet &>(type);
}

/// \copydoc to_integer_range_type(const typet &)
inline integer_range_typet &to_integer_range_type(typet &type)
{
  PRECONDITION(can_cast_type<integer_range_typet>(type));
  return static_cast<integer_range_typet &>(type);
}

bool is_number(const typet &type);

#endif // CPROVER_UTIL_MATHEMATICAL_TYPES_H
