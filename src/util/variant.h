/*******************************************************************\

Module: Include and aliases for an implementation of the C++17
        variant class template. To be replaced by std::variant
        once C++17 support is enabled.

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_VARIANT_H
#define CPROVER_UTIL_VARIANT_H

#include <nonstd/variant.hpp>

using mpark::bad_variant_access;
using mpark::get;
using mpark::get_if;
using mpark::holds_alternative;
using mpark::variant;

#endif // CPROVER_UTIL_VARIANT_H
