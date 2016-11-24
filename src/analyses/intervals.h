/*******************************************************************\

Module: Generic Interval Template

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANALYSIS_INTERVALS_H
#define CPROVER_ANALYSIS_INTERVALS_H

#include <util/ieee_float.h>
#include <util/mp_arith.h>

// a generic weak (but possibly open) interval

template<typename T>
class interval_templatet
{
public:
  bool lower_set, upper_set;
  T lower, upper;

  // construct from singleton  
  explicit interval_templatet(const T &value):
    lower_set(true), upper_set(true),
    lower(value), upper(value)
  {
  }
  
  // 'top' is the default
  inline interval_templatet():
    lower_set(false), upper_set(false)
  { }

  inline void set_lower(const T &value)
  {
    lower_set=true;
    lower=value;
  }

  inline void set_upper(const T &value)
  {
    upper_set=true;
    upper=value;
  }
  
  // is this 'true'?
  inline bool is_top() const
  {
    return !lower_set && !upper_set;
  }
  
  // is this 'false'?
  inline bool is_bottom() const
  {
    return lower_set && upper_set && lower>upper;
  }

  // constraints
  bool make_le_than(const T &value); // upper bound
  bool make_ge_than(const T &value); // lower bound
  
  // Union or disjunction
  bool join(const interval_templatet<T> &other);

  // Intersection or conjunction
  bool meet(const interval_templatet<T> &other);
};

// return 'true' if there is change
template<typename T>
bool interval_templatet<T>::make_le_than(const T &other)
{
  if(!upper_set)
  {
    set_upper(other);
    return true;
  }
  else if(upper>other)
  {
    // new, tighter upper bound
    upper=other;
    return true;
  }
  
  return false;
}

// return 'true' if there is change
template<typename T>
bool interval_templatet<T>::make_ge_than(const T &other)
{
  if(!lower_set)
  {
    set_lower(other);
    return true;
  }
  else if(lower<other)
  {
    // new, tighter lower bound
    lower=other;
    return true;
  }
  
  return false;
}

// Union or disjunction
// return 'true' if there is change
template<typename T>
bool interval_templatet<T>::join(const interval_templatet<T> &other)
{
  bool result=false;

  if(upper_set)
  {
    if(!other.upper_set)
    {
      upper_set=false;
      result=true;
    }
    else if(upper<other.upper)
    {
      // new, looser upper bound
      set_upper(other.upper);
      result=true;
    }
  }

  if(lower_set)
  {
    if(!other.lower_set)
    {
      lower_set=false;
      result=true;
    }
    else if(lower>other.lower)
    {
      // new, looser lower bound
      set_lower(other.lower);
      result=true;
    }
  }

  return result;
}

// Intersection or conjunction
// return 'true' if there is change

template<typename T>
bool interval_templatet<T>::meet(const interval_templatet<T> &other)
{
  bool result=false;

  if(other.upper_set)
    if(!upper_set || upper>other.upper)
    {
      // new, tighter upper bound
      set_upper(other.upper);
      result=true;
    }

  if(other.lower_set)
    if(!lower_set || lower<other.lower)
    {
      // new, tighter lower bound
      set_lower(other.lower);
      result=true;
    }

  return result;
}

typedef interval_templatet<mp_integer> integer_intervalt;
typedef interval_templatet<ieee_floatt> ieee_float_intervalt;

#endif
