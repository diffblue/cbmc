/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_ARITH_TOOLS_H
#define CPROVER_UTIL_ARITH_TOOLS_H

#include "invariant.h"
#include "mp_arith.h"
#include "std_expr.h"

#include <limits>

class typet;

/// Convert a constant expression \p expr to an arbitrary-precision integer.
/// \param  expr: Source expression
/// \param [out] int_value: Integer value (only modified if conversion succeeds)
/// \return False if, and only if, the conversion was successful.
bool to_integer(const constant_exprt &expr, mp_integer &int_value);

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
  std::optional<mp_integer> operator()(const exprt &expr) const
  {
    if(!expr.is_constant())
      return {};
    else
      return operator()(to_constant_expr(expr));
  }

  std::optional<mp_integer> operator()(const constant_exprt &expr) const
  {
    mp_integer out;
    if(to_integer(expr, out))
      return {};
    else
      return out;
  }
};

template <typename Tag>
struct numeric_castt<named_mp_integert<Tag>> final
{
  std::optional<named_mp_integert<Tag>> operator()(const exprt &expr) const
  {
    if(expr.id() != ID_constant)
      return {};
    else
      return operator()(to_constant_expr(expr));
  }

  std::optional<named_mp_integert<Tag>>
  operator()(const constant_exprt &expr) const
  {
    mp_integer out;
    if(to_integer(expr, out))
      return {};
    else
      return named_mp_integert<Tag>{out};
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
  std::optional<T> operator()(const mp_integer &mpi) const
  {
    static_assert(
      std::numeric_limits<T>::max() <=
          std::numeric_limits<decltype(get_val(mpi))>::max() &&
        std::numeric_limits<T>::min() >=
          std::numeric_limits<decltype(get_val(mpi))>::min(),
      "Numeric cast only works for types smaller than long long");

    if(
      mpi <= std::numeric_limits<T>::max() &&
      mpi >= std::numeric_limits<T>::min())
      // to_long converts to long long which is the largest signed numeric type
      return static_cast<T>(get_val(mpi));
    else
      return std::nullopt;
  }

  // Conversion from expression
  std::optional<T> operator()(const exprt &expr) const
  {
    if(expr.is_constant())
      return numeric_castt<T>{}(to_constant_expr(expr));
    else
      return std::nullopt;
  }

  // Conversion from expression
  std::optional<T> operator()(const constant_exprt &expr) const
  {
    if(auto mpi_opt = numeric_castt<mp_integer>{}(expr))
      return numeric_castt<T>{}(*mpi_opt);
    else
      return std::nullopt;
  }
};

/// Converts an expression to any integral type
/// \tparam Target: type to convert to
/// \param arg: expression to convert
/// \return optional integer of type Target if conversion is possible, empty
///   optional otherwise.
template <typename Target>
std::optional<Target> numeric_cast(const exprt &arg)
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

template <typename Target, typename Tag>
Target numeric_cast_v(const named_mp_integert<Tag> &arg)
{
  const auto maybe = numeric_castt<Target>{}(arg.get());
  INVARIANT(maybe, "bits should be convertible to target integral type");
  return *maybe;
}

/// Convert an expression to integral type Target
/// An invariant will fail if the conversion is not possible.
/// \tparam Target: type to convert to
/// \param arg: constant expression
/// \return value of type Target
template <typename Target>
Target numeric_cast_v(const constant_exprt &arg)
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
template <typename Tag>
inline constant_exprt
from_integer(const named_mp_integert<Tag> &int_value, const typet &type)
{
  return from_integer(int_value.get(), type);
}

// ceil(log2(size))
std::size_t address_bits(const mp_integer &size);

mp_integer power(const mp_integer &base, const mp_integer &exponent);

void mp_min(mp_integer &a, const mp_integer &b);
void mp_max(mp_integer &a, const mp_integer &b);

bool get_bvrep_bit(
  const irep_idt &src,
  std::size_t width,
  std::size_t bit_index);

irep_idt
make_bvrep(const std::size_t width, const std::function<bool(std::size_t)> f);

irep_idt integer2bvrep(const mp_integer &, std::size_t width);
mp_integer bvrep2integer(const irep_idt &, std::size_t width, bool is_signed);

#endif // CPROVER_UTIL_ARITH_TOOLS_H
