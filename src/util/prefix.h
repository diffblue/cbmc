/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_PREFIX_H
#define CPROVER_UTIL_PREFIX_H

#include <string>

inline bool has_prefix(const std::string &s, const std::string &prefix)
{
  return s.compare(0, prefix.size(), prefix)==0;
}

#endif
