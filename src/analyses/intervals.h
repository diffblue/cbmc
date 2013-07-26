/*******************************************************************\

Module: Generic Interval Template

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANALYSIS_INTERVALS_H
#define CPROVER_ANALYSIS_INTERVALS_H

#include <util/ieee_float.h>
#include <util/mp_arith.h>

template<typename T>
class interval_templatet
{
public:
  bool lower_set, upper_set;
  T lower, upper;
  
  // 'top' is the default
  inline interval_templatet():lower_set(false), upper_set(false) { }

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
  
  inline bool is_top() const
  {
    return !lower_set && !upper_set;
  }
};

typedef interval_templatet<mp_integer> integer_intervalt;
typedef interval_templatet<ieee_floatt> ieee_float_intervalt;

#endif
