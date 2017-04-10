/*******************************************************************\

Module: Really simple unique_ptr utilities

Author: Reuben Thomas, reuben.thomas@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_MAKE_UNIQUE_H
#define CPROVER_UTIL_MAKE_UNIQUE_H

#include <memory> // unique_ptr

template<typename T, typename... Ts>
std::unique_ptr<T> util_make_unique(Ts &&... ts)
{
  return std::unique_ptr<T>(new T(std::forward<Ts>(ts)...));
}

#endif
