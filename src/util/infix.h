/*******************************************************************\

Module: String infix shorthand

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// String infix shorthand

#ifndef CPROVER_UTIL_INFIX_H
#define CPROVER_UTIL_INFIX_H

#include <string>

inline bool has_infix(
  const std::string &s,
  const std::string &infix,
  size_t offset)
{
  return s.compare(offset, infix.size(), infix)==0;
}

#endif
