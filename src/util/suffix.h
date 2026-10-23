/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_SUFFIX_H
#define CPROVER_UTIL_SUFFIX_H

#include <string>

// C++20 will have std::string_view::ends_with.
// The arguments of has_suffix should be a std::string_view,
// but this triggers a false alarm in gcc when attempting to
// map the comparison to __builtin_memcmp.
inline bool has_suffix(const std::string &s, const std::string &suffix)
{
  if(suffix.size()>s.size())
    return false;
  return s.compare(s.size()-suffix.size(), std::string::npos, suffix)==0;
}

#endif // CPROVER_UTIL_SUFFIX_H
