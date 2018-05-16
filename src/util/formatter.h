/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_FORMATTER_H
#define CPROVER_UTIL_FORMATTER_H

#include "expr.h"

class formattert;

//! The below enables convenient syntax for feeding
//! formatters and objects into streams, via stream << formatter(o)
template <typename T>
class formatter_containert
{
public:
  explicit formatter_containert(
    formattert &_formatter,
    const T &_o) : formatter(_formatter), o(_o)
  {
  }

  class formattert &formatter;
  const T &o;
};

//! This is an abstract interface for a expr/type formatter
class formattert
{
public:
  // use these
  formatter_containert<exprt> operator()(const exprt &o)
  {
    return formatter_containert<exprt>(*this, o);
  }

  formatter_containert<typet> operator()(const typet &o)
  {
    return formatter_containert<typet>(*this, o);
  }

  formatter_containert<source_locationt> operator()(const source_locationt &o)
  {
    return formatter_containert<source_locationt>(*this, o);
  }

  // overload those
  virtual std::ostream &format(std::ostream &, const exprt &) = 0;
  virtual std::ostream &format(std::ostream &, const typet &) = 0;
  virtual std::ostream &format(std::ostream &, const source_locationt &) = 0;
};

//! enable feeding into output streams
template<typename T>
inline std::ostream &
operator<<(std::ostream &os, formatter_containert<T> c)
{
  return c.formatter.format(os, c.o);
}

//! this is the default debug formatter
class default_debug_formattert:public formattert
{
  std::ostream &format(std::ostream &, const exprt &) override;
  std::ostream &format(std::ostream &, const typet &) override;
  std::ostream &format(std::ostream &, const source_locationt &) override;
};

extern default_debug_formattert default_debug_formatter;

//! this is the debug formatter, defaulting to the above
class debug_formattert:public formattert
{
public:
  debug_formattert():formatter(&default_debug_formatter)
  {
  }

  std::ostream &format(std::ostream &os, const exprt &o) override
  {
    return formatter->format(os, o);
  }

  std::ostream &format(std::ostream &os, const typet &o) override
  {
    return formatter->format(os, o);
  }

  std::ostream &format(std::ostream &os, const source_locationt &o) override
  {
    return formatter->format(os, o);
  }

  formattert *formatter;
};

extern debug_formattert debug_formatter;

#endif // CPROVER_UTIL_FORMATTER_H
