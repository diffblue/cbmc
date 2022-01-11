/*******************************************************************\

Module: Wrapper around CATCH to disable selected compiler warnings

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

#define INCLUDED_VIA_USE_CATCH_H

#include <catch/catch.hpp>

#ifdef _MSC_VER
#include <util/pragma_pop.def>
#endif

/// Add to the end of test tags to mark a test that is expected to fail
#define XFAIL "[.][!shouldfail]"

class irept;
std::ostream &operator<<(std::ostream &os, const irept &value);

#endif // CPROVER_TESTING_UTILS_USE_CATCH_H
