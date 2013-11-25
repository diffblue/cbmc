/*******************************************************************\

Module: Time Stopping

Author: Daniel Kroening

Date: February 2004

\*******************************************************************/

#ifndef CPROVER_TIME_STOPPING_H
#define CPROVER_TIME_STOPPING_H

#include <ostream>
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
  
  inline fine_timet operator-(const fine_timet &other)
  {
    fine_timet tmp=*this;
    tmp.t-=other.t;
    return tmp;
  }
  
  inline fine_timet &operator+=(const fine_timet &other)
  {
    t+=other.t;
    return *this;
  }
  
  inline fine_timet operator+(const fine_timet &other)
  {
    fine_timet tmp=*this;
    tmp.t+=other.t;
    return tmp;
  }
  
  inline unsigned long long get_t() const
  {
    return t;
  }
  
  void clear()
  {
    t=0;
  }
  
  std::string as_string() const;
  
protected:
  unsigned long long t;
};

fine_timet current_time();

std::ostream &operator << (std::ostream &, const fine_timet &);

#endif

