/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_THREEVAL_H
#define CPROVER_THREEVAL_H

#include <iosfwd>

//
// three valued logic
//

class tvt
{
public:
  typedef enum { TV_FALSE, TV_UNKNOWN, TV_TRUE } tv_enumt;

  inline bool is_true() const { return value==TV_TRUE; }
  inline bool is_false() const { return value==TV_FALSE; }
  inline bool is_unknown() const { return value==TV_UNKNOWN; }
  inline bool is_known() const { return value==TV_TRUE || value==TV_FALSE; }

  static inline tvt unknown()
  {
    return tvt(TV_UNKNOWN);
  }

  const char *to_string() const;
  
  inline tv_enumt get_value() const
  {
    return value;
  }

  inline tvt()
  {
  }
  
  inline explicit tvt(bool b):value(b?TV_TRUE:TV_FALSE)
  {
  }

  inline explicit tvt(tv_enumt v):value(v)
  {
  }

  inline friend bool operator ==(const tvt a, const tvt b)
  {
    return a.value==b.value;
  }

  inline friend bool operator !=(const tvt a, const tvt b)
  {
    return a.value!=b.value;
  }

  inline friend tvt operator &&(const tvt a, const tvt b)
  {
    if(a.value==TV_FALSE || b.value==TV_FALSE) return tvt(TV_FALSE);
    if(a.value==TV_TRUE  && b.value==TV_TRUE)  return tvt(TV_TRUE);
    return tvt(TV_UNKNOWN);
  }

  inline friend tvt operator ||(const tvt a, const tvt b)
  {
    if(a.value==TV_TRUE  || b.value==TV_TRUE)  return tvt(TV_TRUE);
    if(a.value==TV_FALSE && b.value==TV_FALSE) return tvt(TV_FALSE);
    return tvt(TV_UNKNOWN);
  }

  inline friend tvt operator !(const tvt a)
  {
    if(a.value==TV_UNKNOWN) return tvt(TV_UNKNOWN);
    if(a.value==TV_TRUE) return tvt(TV_FALSE);
    return tvt(TV_TRUE);
  }

protected:
  tv_enumt value;
};

std::ostream &operator << (std::ostream &out, const tvt &a);

#endif
