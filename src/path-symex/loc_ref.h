/*******************************************************************\

Module: Program Locations

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Locations

#ifndef CPROVER_PATH_SYMEX_LOC_REF_H
#define CPROVER_PATH_SYMEX_LOC_REF_H

#include <iosfwd>

class loc_reft
{
public:
  unsigned loc_number;

  loc_reft next_loc() const
  {
    loc_reft tmp=*this;
    tmp.increase();
    return tmp;
  }

  void increase()
  {
    loc_number++;
  }

  void decrease()
  {
    loc_number--;
  }

  bool is_nil() const
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

  loc_reft &operator++() // this is pre-increment
  {
    increase();
    return *this;
  }

  loc_reft &operator--() // this is pre-decrement
  {
    decrease();
    return *this;
  }

  bool operator<(const loc_reft other) const
  {
    return loc_number<other.loc_number;
  }

  bool operator!=(const loc_reft other) const
  {
    return loc_number!=other.loc_number;
  }

  bool operator==(const loc_reft other) const
  {
    return loc_number==other.loc_number;
  }
};

inline std::ostream &operator<<(std::ostream &out, const loc_reft l)
{
  if(l.is_nil())
    return out << "nil";
  else
    return out << l.loc_number;
}

#endif // CPROVER_PATH_SYMEX_LOC_REF_H
