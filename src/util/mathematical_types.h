/*******************************************************************\

Module: Mathematical types

Author: Daniel Kroening, kroening@kroening.com
        Maria Svorenova, maria.svorenova@diffblue.com

\*******************************************************************/

/// \file
/// Mathematical types

#ifndef CPROVER_UTIL_MATHEMATICAL_TYPES_H
#define CPROVER_UTIL_MATHEMATICAL_TYPES_H

#include "expr_cast.h"
#include "invariant.h"
#include "type.h"

/// Unbounded, signed integers (mathematical integers, not bitvectors)
class integer_typet : public typet
{
public:
  integer_typet() : typet(ID_integer)
  {
  }
};

/// Natural numbers including zero (mathematical integers, not bitvectors)
class natural_typet : public typet
{
public:
  natural_typet() : typet(ID_natural)
  {
  }
};

/// Unbounded, signed rational numbers
class rational_typet : public typet
{
public:
  rational_typet() : typet(ID_rational)
  {
  }
};

/// Unbounded, signed real numbers
class real_typet : public typet
{
public:
  real_typet() : typet(ID_real)
  {
  }
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
    : type_with_subtypest(ID_mathematical_function)
  {
    subtypes().resize(2);
    domain() = _domain;
    codomain() = _codomain;
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

bool is_number(const typet &type);

#endif // CPROVER_UTIL_MATHEMATICAL_TYPES_H
