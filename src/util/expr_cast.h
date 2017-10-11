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

template<typename Ret, typename T>
struct expr_try_dynamic_cast_return_typet final
{
  static_assert(
    !std::is_reference<Ret>::value,
    "Ret must be non-qualified");

  typedef
    typename std::conditional<
      std::is_const<T>::value,
      typename std::add_const<Ret>::type,
      Ret>::type *
    type;
};

} // namespace detail

/// \brief Try to cast a reference to a generic exprt to a specific derived
///    class
/// \tparam T The reference or const reference type to \a TUnderlying to cast
///    to
/// \tparam TExpr The original type to cast from, either exprt or const exprt
/// \param base Reference to a generic \ref exprt
/// \return Ptr to object of type \a TUnderlying
///   or nullptr if \a base is not an instance of \a TUnderlying
template <typename T, typename TExpr>
auto expr_try_dynamic_cast(TExpr &base)
  -> typename detail::expr_try_dynamic_cast_return_typet<T, TExpr>::type
{
  typedef
    typename detail::expr_try_dynamic_cast_return_typet<T, TExpr>::type
    returnt;
  static_assert(
    std::is_same<typename std::decay<TExpr>::type, exprt>::value,
    "Tried to expr_try_dynamic_cast from something that wasn't an exprt");
  static_assert(
    std::is_base_of<exprt, T>::value,
    "The template argument T must be derived from exprt.");
  if(!can_cast_expr<T>(base))
    return nullptr;
  const auto ret=static_cast<returnt>(&base);
  validate_expr(*ret);
  return ret;
}

namespace detail // NOLINT
{

template<typename Ret, typename T>
struct expr_dynamic_cast_return_typet final
{
  static_assert(
    !std::is_reference<Ret>::value,
    "Ret must be non-qualified");

  typedef
    typename std::conditional<
      std::is_const<T>::value,
      typename std::add_const<Ret>::type,
      Ret>::type &
    type;
};

} // namespace detail

/// \brief Cast a reference to a generic exprt to a specific derived class.
/// \tparam T The reference or const reference type to \a TUnderlying to cast to
/// \tparam TExpr The original type to cast from, either exprt or const exprt
/// \param base Reference to a generic \ref exprt
/// \return Reference to object of type \a T
/// \throw std::bad_cast If \a base is not an instance of \a TUnderlying
template<typename T, typename TExpr>
auto expr_dynamic_cast(TExpr &base)
  -> typename detail::expr_dynamic_cast_return_typet<T, TExpr>::type
{
  const auto ret=expr_try_dynamic_cast<T>(base);
  if(ret==nullptr)
    throw std::bad_cast();
  return *ret;
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
auto expr_checked_cast(TExpr &base)
  -> typename detail::expr_dynamic_cast_return_typet<T, TExpr>::type
{
  PRECONDITION(can_cast_expr<T>(base));
  return expr_dynamic_cast<T>(base);
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
