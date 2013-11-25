/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_SUFFIX_H
#define CPROVER_UTIL_SUFFIX_H

#include <string>

inline bool has_suffix(const std::string &s, const std::string &suffix)
{
  if(suffix.size()>s.size()) return false;
  return s.compare(s.size()-suffix.size(), std::string::npos, suffix)==0;
}

#endif
