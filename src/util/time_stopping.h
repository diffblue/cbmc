/*******************************************************************\

Module: Time Stopping

Author: Daniel Kroening

Date: February 2004

\*******************************************************************/

#ifndef CPROVER_TIME_STOPPING_H
#define CPROVER_TIME_STOPPING_H

#include <iosfwd>
#include <string>

class fine_timet
{
public:
  inline fine_timet():t(0)
  {
  }
  
  inline explicit fine_timet(unsigned long long _t):t(_t)
  {
  }
  
  inline unsigned long long get_t() const
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
  inline time_periodt()
  {
  }
  
  inline explicit time_periodt(unsigned long long _t):fine_timet(_t)
  {
  }

  std::string as_string() const;

  inline time_periodt &operator+=(const time_periodt &other)
  {
    t+=other.t;
    return *this;
  }
  
  inline time_periodt operator+(const time_periodt &other)
  {
    time_periodt tmp=*this;
    tmp.t+=other.t;
    return tmp;
  }  

  inline time_periodt operator-(const time_periodt &other)
  {
    return time_periodt(t-other.t);
  }
};

class absolute_timet:public fine_timet
{
public:
  inline absolute_timet()
  {
  }
  
  inline explicit absolute_timet(unsigned long long _t):fine_timet(_t)
  {
  }

  inline time_periodt operator-(const absolute_timet &other)
  {
    return time_periodt(t-other.t);
  }
};

absolute_timet current_time();

std::ostream &operator << (std::ostream &, const time_periodt &);

#endif

