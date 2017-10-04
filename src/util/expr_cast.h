/*******************************************************************\

Module:

Author: Nathan Phillips <Nathan.Phillips@diffblue.com>

\*******************************************************************/

#ifndef CPROVER_UTIL_EXPR_CAST_H
#define CPROVER_UTIL_EXPR_CAST_H

/// \file util/expr_cast.h
/// \brief Templated functions to cast to specific exprt-derived classes

#include <typeinfo>
#include <type_traits>
#include <functional>

#include "invariant.h"
#include "expr.h"
#include "optional.h"

/// \brief Check whether a reference to a generic \ref exprt is of a specific
///   derived class.
///
///   Implement template specializations of this function to enable casting
///
/// \tparam T The exprt-derived class to check for
/// \param base Reference to a generic \ref exprt
/// \return true if \a base is of type \a T
template<typename T> bool can_cast_expr(const exprt &base);

/// Called after casting.  Provides a point to assert on the structure of the
/// expr. By default, this is a no-op, but you can provide an overload to
/// validate particular types.  Should always succeed unless the program has
/// entered an invalid state.  We validate objects at cast time as that is when
/// these checks have been used historically, but it would be reasonable to
/// validate objects in this way at any time.
inline void validate_expr(const exprt &) {}

namespace detail // NOLINT
{

// We hide these functions in a namespace so that only functions that they only
// participate in overload resolution when explicitly requested.

/// \brief Try to cast a reference to a generic exprt to a specific derived
///    class
/// \tparam T The reference or const reference type to \a TUnderlying to cast
///    to
/// \tparam TExpr The original type to cast from, either exprt or const exprt
/// \param base Reference to a generic \ref exprt
/// \return Reference to object of type \a TUnderlying
///   or valueless optional if \a base is not an instance of \a TUnderlying
template <typename T, typename TExpr>
optionalt<std::reference_wrapper<typename std::remove_reference<T>::type>>
expr_try_dynamic_cast(TExpr &base)
{
  typedef typename std::decay<T>::type TUnderlyingt;
  typedef typename std::remove_reference<T>::type TConstt;
  static_assert(
    std::is_same<typename std::remove_const<TExpr>::type, exprt>::value,
    "Tried to expr_try_dynamic_cast from something that wasn't an exprt");
  static_assert(
    std::is_reference<T>::value,
    "Tried to convert exprt & to non-reference type");
  static_assert(
    std::is_base_of<exprt, TUnderlyingt>::value,
    "The template argument T must be derived from exprt.");
  if(!can_cast_expr<TUnderlyingt>(base))
    return {};
  T ret=static_cast<T>(base);
  validate_expr(ret);
  return std::reference_wrapper<TConstt>(ret);
}

/// \brief Try to cast a reference to a generic exprt to a specific derived
///    class
/// \tparam T The reference or const reference type to \a TUnderlying to cast
///    to
/// \tparam TExpr The original type to cast from, either exprt or const exprt
/// \param base Reference to a generic \ref exprt
/// \return Reference to object of type \a TUnderlying
///   or valueless optional if \a base is not an instance of \a TUnderlying
template <typename T, typename TExpr>
optionalt<std::reference_wrapper<typename std::remove_reference<T>::type>>
expr_try_checked_cast(TExpr &base)
{
  typedef typename std::decay<T>::type TUnderlyingt;
  PRECONDITION(can_cast_expr<TUnderlyingt>(base));
  return expr_try_checked_cast<T>(base);
}

} // namespace detail

/// \brief Try to cast a constant reference to a generic exprt to a specific
///   derived class
/// \tparam T The exprt-derived class to cast to
/// \param base Reference to a generic \ref exprt
/// \return Reference to object of type \a T or valueless optional if \a base
///   is not an instance of \a T
template<typename T>
optionalt<std::reference_wrapper<typename std::remove_reference<T>::type>>
expr_try_dynamic_cast(const exprt &base)
{
  return detail::expr_try_dynamic_cast<T>(base);
}

/// \brief Try to cast a reference to a generic exprt to a specific derived
///   class
/// \tparam T The exprt-derived class to cast to
/// \param base Reference to a generic \ref exprt
/// \return Reference to object of type \a T or valueless optional if \a base is
///   not an instance of \a T
template<typename T>
optionalt<std::reference_wrapper<typename std::remove_reference<T>::type>>
expr_try_dynamic_cast(exprt &base)
{
  return detail::expr_try_dynamic_cast<T>(base);
}

/// \brief Try to cast a constant reference to a generic exprt to a specific
///   derived class. Also assert that the expr invariants are not violated.
/// \tparam T The exprt-derived class to cast to
/// \param base Reference to a generic \ref exprt
/// \return Reference to object of type \a T or valueless optional if \a base
///   is not an instance of \a T
template<typename T>
optionalt<std::reference_wrapper<typename std::remove_reference<T>::type>>
expr_try_checked_cast(const exprt &base)
{
  return detail::expr_try_checked_cast<T>(base);
}

/// \brief Try to cast a reference to a generic exprt to a specific derived
///   class. Also assert that the expr invariants are not violated.
/// \tparam T The exprt-derived class to cast to
/// \param base Reference to a generic \ref exprt
/// \return Reference to object of type \a T or valueless optional if \a base is
///   not an instance of \a T
template<typename T>
optionalt<std::reference_wrapper<typename std::remove_reference<T>::type>>
expr_try_checked_cast(exprt &base)
{
  return detail::expr_try_checked_cast<T>(base);
}

namespace detail // NOLINT
{

// We hide these functions in a namespace so that only functions that they only
// participate in overload resolution when explicitly requested.

/// \brief Cast a reference to a generic exprt to a specific derived class.
/// \tparam T The reference or const reference type to \a TUnderlying to cast to
/// \tparam TExpr The original type to cast from, either exprt or const exprt
/// \param base Reference to a generic \ref exprt
/// \return Reference to object of type \a T
/// \throw std::bad_cast If \a base is not an instance of \a TUnderlying
template<typename T, typename TExpr>
T expr_dynamic_cast(TExpr &base)
{
  typedef typename std::decay<T>::type TUnderlyingt;
  static_assert(
    std::is_same<typename std::remove_const<TExpr>::type, exprt>::value,
    "Tried to expr_dynamic_cast from something that wasn't an exprt");
  static_assert(
    std::is_reference<T>::value,
    "Tried to convert exprt & to non-reference type");
  static_assert(
    std::is_base_of<exprt, TUnderlyingt>::value,
    "The template argument T must be derived from exprt.");
  if(!can_cast_expr<TUnderlyingt>(base))
    throw std::bad_cast();
  T ret=static_cast<T>(base);
  validate_expr(ret);
  return ret;
}

/// \brief Cast a reference to a generic exprt to a specific derived class.
///   Also assert that the expression has the expected type.
/// \tparam T The reference or const reference type to \a TUnderlying to cast to
/// \tparam TExpr The original type to cast from, either exprt or const exprt
/// \param base Reference to a generic \ref exprt
/// \return Reference to object of type \a T
/// \throw std::bad_cast If \a base is not an instance of \a TUnderlying
/// \remark If CBMC assertions (PRECONDITION) are set to abort then this will
///   abort rather than throw if \a base is not an instance of \a TUnderlying
template<typename T, typename TExpr>
T expr_checked_cast(TExpr &base)
{
  typedef typename std::decay<T>::type TUnderlyingt;
  PRECONDITION(can_cast_expr<TUnderlyingt>(base));
  return expr_dynamic_cast<T>(base);
}

} // namespace detail

/// \brief Cast a constant reference to a generic exprt to a specific derived
///   class
/// \tparam T The exprt-derived class to cast to
/// \param base Reference to a generic \ref exprt
/// \return Reference to object of type \a T
/// \throw std::bad_cast If \a base is not an instance of \a T
/// \remark If CBMC assertions (PRECONDITION) are set to abort then this will
///   abort rather than throw if \a base is not an instance of \a T
template<typename T>
T expr_dynamic_cast(const exprt &base)
{
  return detail::expr_dynamic_cast<T>(base);
}

/// \brief Cast a reference to a generic exprt to a specific derived class
/// \tparam T The exprt-derived class to cast to
/// \param base Reference to a generic \ref exprt
/// \return Reference to object of type \a T
/// \throw std::bad_cast If \a base is not an instance of \a T
/// \remark If CBMC assertions (PRECONDITION) are set to abort then this will
///   abort rather than throw if \a base is not an instance of \a T
template<typename T>
T expr_dynamic_cast(exprt &base)
{
  return detail::expr_dynamic_cast<T>(base);
}

/// \brief Cast a constant reference to a generic exprt to a specific derived
///   class. Also assert that the exprt invariants are not violated.
/// \tparam T The exprt-derived class to cast to
/// \param base Reference to a generic \ref exprt
/// \return Reference to object of type \a T
/// \throw std::bad_cast If \a base is not an instance of \a T
/// \remark If CBMC assertions (PRECONDITION) are set to abort then this will
///   abort rather than throw if \a base is not an instance of \a T
template<typename T>
T expr_checked_cast(const exprt &base)
{
  return detail::expr_checked_cast<T>(base);
}

/// \brief Cast a reference to a generic exprt to a specific derived class.
///   Also assert that the exprt invariants are not violated.
/// \tparam T The exprt-derived class to cast to
/// \param base Reference to a generic \ref exprt
/// \return Reference to object of type \a T
/// \throw std::bad_cast If \a base is not an instance of \a T
/// \remark If CBMC assertions (PRECONDITION) are set to abort then this will
///   abort rather than throw if \a base is not an instance of \a T
template<typename T>
T expr_checked_cast(exprt &base)
{
  return detail::expr_checked_cast<T>(base);
}

inline void validate_operands(
  const exprt &value,
  exprt::operandst::size_type number,
  const char *message,
  bool allow_more=false)
{
  DATA_INVARIANT(
    allow_more
      ? value.operands().size()>=number
      : value.operands().size()==number,
    message);
}

#endif  // CPROVER_UTIL_EXPR_CAST_H
