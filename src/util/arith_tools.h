/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_ARITH_TOOLS_H
#define CPROVER_UTIL_ARITH_TOOLS_H

#include "invariant.h"
#include "mp_arith.h"
#include "optional.h"
#include "std_expr.h"

#include "deprecate.h"

class typet;

// this one will go away
// returns 'true' on error
/// \deprecated: use the constant_exprt version instead
DEPRECATED("Use the constant_exprt version instead")
bool to_integer(const exprt &expr, mp_integer &int_value);

// returns 'true' on error
bool to_integer(const constant_exprt &expr, mp_integer &int_value);

// returns 'true' on error
bool to_unsigned_integer(const constant_exprt &expr, unsigned &uint_value);

/// Numerical cast provides a unified way of converting from one numerical type
/// to another.
/// Generic case doesn't exist, this has to be specialized for different types.
template <typename Target, typename = void>
struct numeric_castt final
{
};

/// Convert expression to mp_integer
template <>
struct numeric_castt<mp_integer> final
{
  optionalt<mp_integer> operator()(const exprt &expr) const
  {
    mp_integer out;
    if(expr.id() != ID_constant || to_integer(to_constant_expr(expr), out))
      return {};
    return out;
  }
};

/// Convert mp_integer or expr to any integral type
template <typename T>
struct numeric_castt<T,
                     typename std::enable_if<std::is_integral<T>::value>::type>
{
private:
  // Unchecked conversion from mp_integer when T is signed
  template <typename U = T,
            typename std::enable_if<std::is_signed<U>::value, int>::type = 0>
  static auto get_val(const mp_integer &mpi) -> decltype(mpi.to_long())
  {
    return mpi.to_long();
  }

  // Unchecked conversion from mp_integer when T is unsigned
  template <typename U = T,
            typename std::enable_if<!std::is_signed<U>::value, int>::type = 0>
  static auto get_val(const mp_integer &mpi) -> decltype(mpi.to_ulong())
  {
    return mpi.to_ulong();
  }

public:
  // Conversion from mp_integer to integral type T
  optionalt<T> operator()(const mp_integer &mpi) const
  {
#if !defined(_MSC_VER) || _MSC_VER >= 1900
    static_assert(
      std::numeric_limits<T>::max() <=
          std::numeric_limits<decltype(get_val(mpi))>::max() &&
        std::numeric_limits<T>::min() >=
          std::numeric_limits<decltype(get_val(mpi))>::min(),
      "Numeric cast only works for types smaller than long long");
#else
    // std::numeric_limits<> methods are not declared constexpr in old versions
    // of VS
    PRECONDITION(
      std::numeric_limits<T>::max() <=
        std::numeric_limits<decltype(get_val(mpi))>::max() &&
      std::numeric_limits<T>::min() >=
        std::numeric_limits<decltype(get_val(mpi))>::min());
#endif
    if(
      mpi <= std::numeric_limits<T>::max() &&
      mpi >= std::numeric_limits<T>::min())
      // to_long converts to long long which is the largest signed numeric type
      return static_cast<T>(get_val(mpi));
    else
      return {};
  }

  // Conversion from expression
  optionalt<T> operator()(const exprt &expr) const
  {
    if(auto mpi_opt = numeric_castt<mp_integer>{}(expr))
      return numeric_castt<T>{}(*mpi_opt);
    else
      return {};
  }
};

/// Converts an expression to any integral type
/// \tparam Target: type to convert to
/// \param arg: expression to convert
/// \return optional integer of type Target if conversion is possible,
///         empty optional otherwise.
template <typename Target>
optionalt<Target> numeric_cast(const exprt &arg)
{
  return numeric_castt<Target>{}(arg);
}

/// Convert an mp_integer to integral type Target
/// An invariant will fail if the conversion is not possible.
/// \tparam Target: type to convert to
/// \param arg: mp_integer
/// \return value of type Target
template <typename Target>
Target numeric_cast_v(const mp_integer &arg)
{
  const auto maybe = numeric_castt<Target>{}(arg);
  INVARIANT(maybe, "mp_integer should be convertible to target integral type");
  return *maybe;
}

/// Convert an expression to integral type Target
/// An invariant will fail if the conversion is not possible.
/// \tparam Target: type to convert to
/// \param arg: constant expression
/// \return value of type Target
template <typename Target>
Target numeric_cast_v(const exprt &arg)
{
  const auto maybe = numeric_castt<Target>{}(arg);
  INVARIANT_WITH_DIAGNOSTICS(
    maybe,
    "expression should be convertible to target integral type",
    irep_pretty_diagnosticst(arg));
  return *maybe;
}

// PRECONDITION(false) in case of unsupported type
constant_exprt from_integer(const mp_integer &int_value, const typet &type);

// ceil(log2(size))
std::size_t address_bits(const mp_integer &size);

mp_integer power(const mp_integer &base, const mp_integer &exponent);

void mp_min(mp_integer &a, const mp_integer &b);
void mp_max(mp_integer &a, const mp_integer &b);

bool get_bitvector_bit(
  const irep_idt &src,
  std::size_t width,
  std::size_t bit_index);

irep_idt
make_bvrep(const std::size_t width, const std::function<bool(std::size_t)> f);

#endif // CPROVER_UTIL_ARITH_TOOLS_H
