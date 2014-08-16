/*******************************************************************\

Module: Program Locations

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LOC_REF_H
#define CPROVER_LOC_REF_H

#include <iosfwd>

class loc_reft
{
public:
  unsigned loc_number;
  
  inline loc_reft next_loc()
  {
    loc_reft tmp=*this;
    tmp.increase();
    return tmp;
  }
  
  inline void increase()
  {
    loc_number++;
  }
  
  inline void decrease()
  {
    loc_number--;
  }
  
  inline bool is_nil() const
  {
    return loc_number==nil().loc_number;
  }

  loc_reft():loc_number(-1) // ugly conversion
  {
  }  
  
  static inline loc_reft nil()
  {
    return loc_reft();
  }
  
  inline loc_reft &operator++() // this is pre-increment
  {
    increase();
    return *this;
  }

  inline loc_reft &operator--() // this is pre-decrement
  {
    decrease();
    return *this;
  }
};

static inline bool operator < (const loc_reft l1, const loc_reft l2)
{
  return l1.loc_number < l2.loc_number;
}

static inline bool operator != (const loc_reft l1, const loc_reft l2)
{
  return l1.loc_number != l2.loc_number;
}

static inline bool operator == (const loc_reft l1, const loc_reft l2)
{
  return l1.loc_number == l2.loc_number;
}

static inline std::ostream &operator << (std::ostream &out, loc_reft l)
{
  if(l.is_nil())
    return out << "nil";
  else
    return out << l.loc_number;
}

#endif
