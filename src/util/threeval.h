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
  enum class tv_enumt { TV_FALSE, TV_UNKNOWN, TV_TRUE };

  inline bool is_true() const { return value==tv_enumt::TV_TRUE; }
  inline bool is_false() const { return value==tv_enumt::TV_FALSE; }
  inline bool is_unknown() const { return value==tv_enumt::TV_UNKNOWN; }
  inline bool is_known() const { return value==tv_enumt::TV_TRUE || value==tv_enumt::TV_FALSE; }

  static inline tvt unknown()
  {
    return tvt(tv_enumt::TV_UNKNOWN);
  }

  const char *to_string() const;
  
  inline tv_enumt get_value() const
  {
    return value;
  }

  inline tvt()
  {
  }
  
  inline explicit tvt(bool b):value(b?tv_enumt::TV_TRUE:tv_enumt::TV_FALSE)
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
    if(a.value==tv_enumt::TV_FALSE || b.value==tv_enumt::TV_FALSE) return tvt(tv_enumt::TV_FALSE);
    if(a.value==tv_enumt::TV_TRUE  && b.value==tv_enumt::TV_TRUE)  return tvt(tv_enumt::TV_TRUE);
    return tvt(tv_enumt::TV_UNKNOWN);
  }

  inline friend tvt operator ||(const tvt a, const tvt b)
  {
    if(a.value==tv_enumt::TV_TRUE  || b.value==tv_enumt::TV_TRUE)  return tvt(tv_enumt::TV_TRUE);
    if(a.value==tv_enumt::TV_FALSE && b.value==tv_enumt::TV_FALSE) return tvt(tv_enumt::TV_FALSE);
    return tvt(tv_enumt::TV_UNKNOWN);
  }

  inline friend tvt operator !(const tvt a)
  {
    if(a.value==tv_enumt::TV_UNKNOWN) return tvt(tv_enumt::TV_UNKNOWN);
    if(a.value==tv_enumt::TV_TRUE) return tvt(tv_enumt::TV_FALSE);
    return tvt(tv_enumt::TV_TRUE);
  }

protected:
  tv_enumt value;
};

std::ostream &operator << (std::ostream &out, const tvt &a);

#endif
