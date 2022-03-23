/*******************************************************************\

Module: typedef for optional class template. New code should directly
        use std::optional.

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_OPTIONAL_H
#define CPROVER_UTIL_OPTIONAL_H

#include <optional>

template <typename T>
using optionalt = std::optional<T>; // NOLINT template typedef

#endif // CPROVER_UTIL_OPTIONAL_H
