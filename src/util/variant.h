/*******************************************************************\

Module: typedef for variant class template. To be replaced with
        std::variant once C++17 support is enabled

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_VARIANT_H
#define CPROVER_UTIL_VARIANT_H

#include <mpark/variant.hpp>

template <typename... Ts>
using variantt = mpark::variant<Ts...>;

#endif // CPROVER_UTIL_VARIANT_H
