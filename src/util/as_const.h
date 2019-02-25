/*******************************************************************\

Module: Util

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_AS_CONST_H
#define CPROVER_UTIL_AS_CONST_H

/// Return a reference to the same object but ensures the type is const
template <typename T>
const T &as_const(T &value)
{
  return static_cast<const T &>(value);
}

#endif // CPROVER_UTIL_AS_CONST_H
