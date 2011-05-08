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
  return std::string(s, s.size()-suffix.size(), std::string::npos)==suffix;
}

#endif
