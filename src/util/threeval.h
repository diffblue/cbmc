/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_THREEVAL_H
#define CPROVER_THREEVAL_H

#include <ostream>

//
// three valued logic
//

class tvt
{
public:
  typedef enum { TV_FALSE, TV_UNKNOWN, TV_TRUE } tv_enumt;

  bool is_true() const { return value==TV_TRUE; }
  bool is_false() const { return value==TV_FALSE; }
  bool is_unknown() const { return value==TV_UNKNOWN; }
  bool is_known() const { return value==TV_TRUE || value==TV_FALSE; }

  const char *to_string() const;
  
  tv_enumt get_value() const
  {
    return value;
  }

  tvt()
  {
  }
  
  explicit tvt(bool b):value(b?TV_TRUE:TV_FALSE)
  {
  }

  explicit tvt(tv_enumt v):value(v)
  {
  }

  friend bool operator ==(const tvt a, const tvt b)
  {
    return a.value==b.value;
  }

  friend bool operator !=(const tvt a, const tvt b)
  {
    return a.value!=b.value;
  }

  friend tvt operator &&(const tvt a, const tvt b)
  {
    if(a.value==TV_FALSE || b.value==TV_FALSE) return tvt(TV_FALSE);
    if(a.value==TV_TRUE  && b.value==TV_TRUE)  return tvt(TV_TRUE);
    return tvt(TV_UNKNOWN);
  }

  friend tvt operator ||(const tvt a, const tvt b)
  {
    if(a.value==TV_TRUE  || b.value==TV_TRUE)  return tvt(TV_TRUE);
    if(a.value==TV_FALSE && b.value==TV_FALSE) return tvt(TV_FALSE);
    return tvt(TV_UNKNOWN);
  }

  friend tvt operator !(const tvt a)
  {
    if(a.value==TV_UNKNOWN) return tvt(TV_UNKNOWN);
    if(a.value==TV_TRUE) return tvt(TV_FALSE);
    return tvt(TV_TRUE);
  }

  friend std::ostream &operator << (std::ostream &out, const tvt &a)
  {
    return out << a.to_string();
  }

protected:
  tv_enumt value;
};


#endif
