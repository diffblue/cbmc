/*******************************************************************\

Module:

Author: Reuben Thomas, reuben.thomas@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_FREER_H
#define CPROVER_UTIL_FREER_H

#include <cstdlib>
#include <utility>

struct freert
{
  template <typename T>
  void operator()(T &&t) const
  {
    free(std::forward<T>(t));
  }
};

#endif
