/*******************************************************************\

Module: typedef for optional class template. New code should directly
        use std::optional.

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_OPTIONAL_H
#define CPROVER_UTIL_OPTIONAL_H

#include "deprecate.h"

#include <optional>

template <typename T>
using optionalt
#ifndef _WIN32
  // Visual Studio doesn't support [deprecated] in this place
  DEPRECATED(SINCE(2023, 11, 17, "directly use std::optional instead")) =
#else
  =
#endif
    std::optional<T>; // NOLINT template typedef

#endif // CPROVER_UTIL_OPTIONAL_H
