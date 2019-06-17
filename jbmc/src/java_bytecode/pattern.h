/*******************************************************************\

Module: Pattern matching for bytecode instructions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pattern matching for bytecode instructions

#ifndef CPROVER_JAVA_BYTECODE_PATTERN_H
#define CPROVER_JAVA_BYTECODE_PATTERN_H

#include "bytecode_info.h"

/// Given a string of the format '?blah?', will return true when compared
/// against a string that matches appart from any characters that are '?'
/// in the original string. Equivalent to doing a regex match on '.blah.'
class patternt
{
public:
  explicit patternt(const char *_p) : p(_p)
  {
  }

  // match with '?'
  bool operator==(const u1 bytecode) const
  {
    const char *what = bytecode_info[bytecode].mnemonic;

    std::size_t i;

    for(i = 0; what[i] != 0; i++)
      if(p[i] == 0)
        return false;
      else if(p[i] != '?' && p[i] != what[i])
        return false;

    return p[i] == 0;
  }

  friend bool operator==(const u1 bytecode, const patternt &p)
  {
    return p == bytecode;
  }

  friend bool operator!=(const u1 bytecode, const patternt &p)
  {
    return !(p == bytecode);
  }

protected:
  const char *p;
};

#endif // CPROVER_JAVA_BYTECODE_PATTERN_H
