/*******************************************************************\

Module: Narrowing conversion functions

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_NARROW_H
#define CPROVER_UTIL_NARROW_H

#include <type_traits>

#include "invariant.h"

/// Alias for static_cast intended to be used for numeric casting
/// Rationale: Easier to grep than static_cast
template <typename output_type, typename input_type>
output_type narrow_cast(input_type value)
{
  static_assert(
    std::is_arithmetic<input_type>::value &&
      std::is_arithmetic<output_type>::value,
    "narrow_cast is intended only for numeric conversions");
  return static_cast<output_type>(value);
}

/// Run-time checked narrowing cast. Raises an invariant if the input
/// value cannot be converted to the output value without data loss
///
/// Template accepts a single argument - the return type. Input type
/// is deduced from the function argument and shouldn't be specified
template <typename output_type, typename input_type>
output_type narrow(input_type input)
{
  const auto output = static_cast<output_type>(input);
  INVARIANT(static_cast<input_type>(output) == input, "Data loss detected");
  return output;
}

/// Run-time checked narrow cast. Throws a std::out_of_range error
/// if the input cannot be converted to the output_type without data lass
template <typename output_type, typename input_type>
output_type narrow_or_throw_out_of_range(input_type input)
{
  auto const result = narrow_cast<output_type>(input);
  // The round trip alone misses a sign change when the two types have the
  // same width (unsigned(-1L) converts back to -1L where long is 32 bits).
  bool sign_changed = false;
  if constexpr(
    std::is_signed<input_type>::value != std::is_signed<output_type>::value)
  {
    sign_changed = (input < input_type{}) != (result < output_type{});
  }
  if(static_cast<input_type>(result) != input || sign_changed)
  {
    throw std::out_of_range{"narrowing gave a different value than expected"};
  }
  return result;
}

#endif // CPROVER_UTIL_NARROW_H
