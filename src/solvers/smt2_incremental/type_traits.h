// Author: Diffblue Ltd.

/// \file
/// Back ports of utilities available in the `<type_traits>` library for C++14
/// or C++17 to C++11. These can be replaced with the standard library versions
/// as and when we upgrade the version CBMC is compiled with.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_TYPE_TRAITS_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_TYPE_TRAITS_H

#include <type_traits>

namespace detail // NOLINT
{
// Implementation detail of `void_t`.
template <typename... typest>
struct make_voidt
{
  using type = void;
};
} // namespace detail

// The below definition is of a back-ported version of the C++17 STL
// `std::void_t` template. This makes this particular template available when
// compiling for the C++11 or C++14 standard versions. It will also compile
// as-is when targeting the C++17 standard. The back-ported version is not added
// to the `std` namespace as this would be undefined behaviour. However once we
// permanently move to the new standard the below code should be removed
// and `std::void_t` should be used directly, to avoid polluting the global
// namespace. For example -
//   `void_t<decltype(foo.bar())>`
// should be updated to -
//   `std::void_t<decltype(foo.bar())>`
template <typename... typest>
using void_t = typename detail::make_voidt<typest...>::type;

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_TYPE_TRAITS_H
