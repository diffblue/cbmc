/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_PREFIX_H
#define CPROVER_UTIL_PREFIX_H

#include <string>

inline bool has_prefix(const std::string &s, const std::string &prefix)
{
  return std::string(s, 0, prefix.size())==prefix;
}

#endif
