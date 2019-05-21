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

/// Return a pointer to the same object but ensures the type is pointer to const
template <typename T>
const T *as_const_ptr(T *t)
{
  return t;
}

/// Deleted to avoid calling as_const on an xvalue
template <typename T>
void as_const(T &&) = delete;

#endif // CPROVER_UTIL_AS_CONST_H
