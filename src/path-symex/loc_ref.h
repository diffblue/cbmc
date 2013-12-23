/*******************************************************************\

Module: Program Locations

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LOC_REF_H
#define CPROVER_LOC_REF_H

#include <ostream>

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

  loc_reft():loc_number(-1)
  {
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
  return out << l.loc_number;
}

#endif
