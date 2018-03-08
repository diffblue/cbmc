/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_FORMAT_H
#define CPROVER_UTIL_FORMAT_H

#include <iosfwd>

//! The below enables convenient syntax for feeding
//! objects into streams, via stream << format(o)
template <typename T>
class format_containert
{
public:
  explicit format_containert(const T &_o) : o(_o)
  {
  }

  const T &o;
};

template <typename T>
static inline std::ostream &
operator<<(std::ostream &os, const format_containert<T> &f)
{
  return format_rec(os, f.o);
}

template <typename T>
static inline format_containert<T> format(const T &o)
{
  return format_containert<T>(o);
}

#endif // CPROVER_UTIL_FORMAT_H
