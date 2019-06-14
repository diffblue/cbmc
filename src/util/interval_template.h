/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_INTERVAL_TEMPLATE_H
#define CPROVER_UTIL_INTERVAL_TEMPLATE_H

#include <algorithm>
#include <iosfwd>
#include <ostream>

#include "threeval.h"

template<class T> class interval_templatet
{
public:
  interval_templatet():lower_set(false), upper_set(false)
  {
    // this is 'top'
  }

  explicit interval_templatet(const T &x):
    lower_set(true),
    upper_set(true),
    lower(x),
    upper(x)
  {
  }

  explicit interval_templatet(const T &l, const T &u):
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

  bool is_bottom() const // equivalent to 'false'
  {
    return empty();
  }

  bool is_top() const // equivalent to 'true'
  {
    return !lower_set && !upper_set;
  }

  bool singleton() const
  {
    return upper_set && lower_set && lower==upper;
  }

  // constraints
  void make_le_than(const T &v) // add upper bound
  {
    if(upper_set)
    {
      if(upper>v)
        upper=v;
    }
    else
    {
      upper_set=true;
      upper=v;
    }
  }

  void make_ge_than(const T &v) // add lower bound
  {
    if(lower_set)
    {
      if(lower<v)
        lower=v;
    }
    else
    {
      lower_set=true;
      lower=v;
    }
  }

  // Union or disjunction
  void join(const interval_templatet<T> &i)
  {
    approx_union_with(i);
  }

  // Intersection or conjunction
  void meet(const interval_templatet<T> &i)
  {
    intersect_with(i);
  }

  void intersect_with(const interval_templatet &i)
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

  void approx_union_with(const interval_templatet &i)
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
tvt operator<=(const interval_templatet<T> &a, const interval_templatet<T> &b)
{
  if(a.upper_set && b.lower_set && a.upper<=b.lower)
    return tvt(true);
  if(a.lower_set && b.upper_set && a.lower>b.upper)
    return tvt(false);

  return tvt::unknown();
}

template<class T>
tvt operator>=(const interval_templatet<T> &a, const interval_templatet<T> &b)
{
  return b<=a;
}

template<class T>
tvt operator<(const interval_templatet<T> &a, const interval_templatet<T> &b)
{
  return !(a>=b);
}

template<class T>
tvt operator>(const interval_templatet<T> &a, const interval_templatet<T> &b)
{
  return !(a<=b);
}

template<class T>
bool operator==(const interval_templatet<T> &a, const interval_templatet<T> &b)
{
  if(a.lower_set!=b.lower_set)
    return false;
  if(a.upper_set!=b.upper_set)
    return false;

  if(a.lower_set && a.lower!=b.lower)
    return false;
  if(a.upper_set && a.upper!=b.upper)
    return false;

  return true;
}

template<class T>
bool operator!=(const interval_templatet<T> &a, const interval_templatet<T> &b)
{
  return !(a==b);
}

template<class T>
interval_templatet<T> upper_interval(const T &u)
{
  interval_templatet<T> i;
  i.upper_set=true;
  i.upper=u;
  return i;
}

template<class T>
interval_templatet<T> lower_interval(const T &l)
{
  interval_templatet<T> i;
  i.lower_set=true;
  i.lower=l;
  return i;
}

template<class T>
std::ostream &operator << (std::ostream &out, const interval_templatet<T> &i)
{
  if(i.lower_set)
    out << '[' << i.lower;
  else
    out << ")-INF";

  out << ',';

  if(i.upper_set)
    out << i.upper << ']';
  else
    out << "+INF(";

  return out;
}

#endif // CPROVER_UTIL_INTERVAL_TEMPLATE_H
