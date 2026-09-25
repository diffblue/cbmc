/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_PREFIX_H
#define CPROVER_UTIL_PREFIX_H

#include <string_view>

// C++20 will have std::string_view::starts_with

inline bool has_prefix(std::string_view s, std::string_view prefix)
{
  return s.compare(0, prefix.size(), prefix)==0;
}

#endif // CPROVER_UTIL_PREFIX_H
