/*******************************************************************\

Module: Wrapper around CATCH to disable selected compiler warnings
        and add pretty printing for failure messages involving ireps.

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_TESTING_UTILS_USE_CATCH_H
#define CPROVER_TESTING_UTILS_USE_CATCH_H

#ifdef _MSC_VER
#include <util/pragma_push.def>
#pragma warning(disable : 4061)
// enumerator not explicitly handled by case label
#pragma warning(disable : 4388)
// signed/unsigned mismatch
#pragma warning(disable : 4668)
// using #if/#elif on undefined macro
#pragma warning(disable : 4628)
// digraphs not supported with -Ze
#pragma warning(disable : 4583)
// destructor is not implicitly called
#pragma warning(disable : 4868)
// compiler may not enforce left-to-right evaluation order in braced initializer
// list
#pragma warning(disable : 4365)
// signed/unsigned mismatch
#endif

#include <string>
#include <type_traits>
#include <util/irep.h>

/// Returns true if `potential_irept` is an `irept`.
template <typename potential_irept>
constexpr bool is_irep()
{
  return std::is_convertible<potential_irept, irept>::value;
}

/// Default case for stringify fallback printing.
template <typename unknownt, typename = void>
struct catch_fallback_stringifyt
{
  template <typename anyt>
  std::string operator()(anyt &&any)
  {
    return "{?}";
  }
};

/// Stringify fallback printing specialization for irept.
template <typename potentially_an_irept>
struct catch_fallback_stringifyt<
  potentially_an_irept,
  typename std::enable_if<is_irep<potentially_an_irept>()>::type>
{
  template <typename any_irept>
  std::string operator()(any_irept &&any_irep)
  {
    return any_irep.pretty(0, 0);
  }
};

template <typename unknownt>
std::string catch_fallback_stringify(unknownt &&unknown)
{
  return catch_fallback_stringifyt<typename std::decay<unknownt>::type>{}(
    std::forward<unknownt>(unknown));
}

// Replace catch's original stringify fallback with a custom version which
// pretty prints ireps.
#define CATCH_CONFIG_FALLBACK_STRINGIFIER(x) catch_fallback_stringify(x);

#define INCLUDED_VIA_USE_CATCH_H

#include <catch/catch.hpp>

#ifdef _MSC_VER
#include <util/pragma_pop.def>
#endif

/// Add to the end of test tags to mark a test that is expected to fail
#define XFAIL "[.][!shouldfail]"

#endif // CPROVER_TESTING_UTILS_USE_CATCH_H
