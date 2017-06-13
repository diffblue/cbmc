/*******************************************************************\

Module: Time Stopping

Author: Daniel Kroening

Date: February 2004

\*******************************************************************/

/// \file
/// Time Stopping

#ifndef CPROVER_UTIL_TIME_STOPPING_H
#define CPROVER_UTIL_TIME_STOPPING_H

#include <iosfwd>
#include <string>

class fine_timet
{
public:
  fine_timet():t(0)
  {
  }

  explicit fine_timet(unsigned long long _t):t(_t)
  {
  }

  unsigned long long get_t() const
  {
    return t;
  }

  void clear()
  {
    t=0;
  }

protected:
  unsigned long long t;
};

class time_periodt:public fine_timet
{
public:
  time_periodt()
  {
  }

  explicit time_periodt(unsigned long long _t):fine_timet(_t)
  {
  }

  std::string as_string() const;

  time_periodt &operator+=(const time_periodt &other)
  {
    t+=other.t;
    return *this;
  }

  time_periodt operator+(const time_periodt &other)
  {
    time_periodt tmp=*this;
    tmp.t+=other.t;
    return tmp;
  }

  time_periodt operator-(const time_periodt &other)
  {
    return time_periodt(t-other.t);
  }
};

class absolute_timet:public fine_timet
{
public:
  absolute_timet()
  {
  }

  explicit absolute_timet(unsigned long long _t):fine_timet(_t)
  {
  }

  time_periodt operator-(const absolute_timet &other)
  {
    return time_periodt(t-other.t);
  }
};

absolute_timet current_time();

std::ostream &operator << (std::ostream &, const time_periodt &);

#endif // CPROVER_UTIL_TIME_STOPPING_H
