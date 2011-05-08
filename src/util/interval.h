/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_INTERVAL_H
#define CPROVER_INTERVAL_H

#include <iostream>

#include "threeval.h"

template<class T> class interval
{
public:
  interval():lower_set(false), upper_set(false)
  {
  }
  
  explicit interval(const T &x):
    lower_set(true),
    upper_set(true),
    lower(x),
    upper(x)
  {
  }
  
  explicit interval(const T &l, const T &u):
    lower_set(true),
    upper_set(true),
    lower(l),
    upper(u)
  {
  }
  
  bool lower_set, upper_set;
  T lower, upper;
  
  const T &get_lower() const
  {
    return lower;
  }
  
  const T &get_upper() const
  {
    return upper;
  }
  
  bool empty() const
  {
    return upper_set && lower_set && lower>upper;
  }
  
  bool singleton() const
  {
    return upper_set && lower_set && lower==upper;
  }
  
  void intersect_with(const interval &i)
  {
    if(i.lower_set)
    {
      if(lower_set)
      {
        lower=std::max(lower, i.lower);
      }
      else
      {
        lower_set=true;
        lower=i.lower;
      }
    }
    
    if(i.upper_set)
    {
      if(upper_set)
      {
        upper=std::min(upper, i.upper);
      }
      else
      {
        upper_set=true;
        upper=i.upper;
      }
    }
  }

  void approx_union_with(const interval &i)
  {
    if(i.lower_set && lower_set)
      lower=std::min(lower, i.lower);
    else if(!i.lower_set && lower_set)
      lower_set=false;
    
    if(i.upper_set && upper_set)
      upper=std::max(upper, i.upper);
    else if(!i.upper_set && upper_set)
      upper_set=false;
  }
};

template<class T>
tvt operator <= (const interval<T> &a, const interval<T> &b)
{
  if(a.upper_set && b.lower_set && a.upper<=b.lower) return tvt(true);
  if(a.lower_set && b.upper_set && a.lower>b.upper) return tvt(false);
  return tvt(tvt::TV_UNKNOWN);
}

template<class T>
tvt operator >= (const interval<T> &a, const interval<T> &b)
{
  return b<=a;
}

template<class T>
tvt operator <  (const interval<T> &a, const interval<T> &b)
{
  return !(a>=b);
}

template<class T>
tvt operator >  (const interval<T> &a, const interval<T> &b)
{
  return !(a<=b);
}

template<class T>
tvt operator == (const interval<T> &a, const interval<T> &b)
{
  if(a.lower_set!=b.lower_set) return tvt(false);
  if(a.upper_set!=b.upper_set) return tvt(false);
  if(a.lower_set && a.lower!=b.lower) return tvt(false);
  if(a.upper_set && a.upper!=b.upper) return tvt(false);  
  return tvt(true);
}

template<class T>
tvt operator != (const interval<T> &a, const interval<T> &b)
{
  return !(a==b);
}

template<class T>
interval<T> upper_interval(const T &u)
{
  interval<T> i;
  i.upper_set=true;
  i.upper=u;
  return i;
}

template<class T>
interval<T> lower_interval(const T &l)
{
  interval<T> i;
  i.lower_set=true;
  i.lower=l;
  return i;
}

template<class T>
std::ostream &operator << (std::ostream &out, const interval<T> &i)
{
  if(i.lower_set)
    out << "[" << i.lower;
  else
    out << ")-INF";
  
  out << ",";
  
  if(i.upper_set)
    out << i.upper << "]";
  else
    out << "+INF(";
  
  return out;
}

#endif
