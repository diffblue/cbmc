/*******************************************************************\

Module: String infix shorthand

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// String infix shorthand

#ifndef CPROVER_UTIL_INFIX_H
#define CPROVER_UTIL_INFIX_H

#include <string_view>

inline bool has_infix(std::string_view s, std::string_view infix, size_t offset)
{
  return s.compare(offset, infix.size(), infix)==0;
}

#endif
