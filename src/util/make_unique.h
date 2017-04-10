/*******************************************************************\

Module: Really simple unique_ptr utilities

Author: Reuben Thomas, reuben.thomas@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_MAKE_UNIQUE_H
#define CPROVER_UTIL_MAKE_UNIQUE_H

#include <memory> // unique_ptr

// This is a stand-in for std::make_unique, which isn't part of the standard
// library until C++14.  When we move to C++14, we should do a find-and-replace
// on this to use std::make_unique instead.

template<typename T, typename... Ts>
std::unique_ptr<T> util_make_unique(Ts &&... ts)
{
  return std::unique_ptr<T>(new T(std::forward<Ts>(ts)...));
}

#endif
