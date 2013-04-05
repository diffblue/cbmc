/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_C_QUALIFIERS_H
#define CPROVER_ANSI_C_C_QUALIFIERS_H

#include <ostream>

#include <expr.h>

class c_qualifierst
{
public:
  c_qualifierst()
  {
    clear();
  }
  
  explicit c_qualifierst(const typet &src)
  {
    clear();
    read(src);
  }
  
  void clear()
  {
    is_constant=false;
    is_volatile=false;
    is_restricted=false;
    is_ptr32=is_ptr64=false;
    is_transparent_union=false;
  }

  // standard ones
  bool is_constant, is_volatile, is_restricted;
  
  // MS Visual Studio extension
  bool is_ptr32, is_ptr64;
  
  // gcc extension
  bool is_transparent_union;
  
  // will likely add alignment here as well
  
  std::string as_string() const;
  void read(const typet &src);
  void write(typet &src) const;
  
  static void clear(typet &dest);
  
  bool is_subset_of(const c_qualifierst &q) const
  {
    return (!is_constant || q.is_constant) &&
           (!is_volatile || q.is_volatile) &&
           (!is_restricted || q.is_restricted) &&
           (!is_ptr32 || q.is_ptr32) &&
           (!is_ptr64 || q.is_ptr64);

    // is_transparent_union isn't checked
  }
  
  friend bool operator == (
    const c_qualifierst &a,
    const c_qualifierst &b)
  {
    return a.is_constant==b.is_constant &&
           a.is_volatile==b.is_volatile &&
           a.is_restricted==b.is_restricted &&
           a.is_ptr32==b.is_ptr32 &&
           a.is_ptr64==b.is_ptr64 &&
           a.is_transparent_union==b.is_transparent_union;
  }

  friend bool operator != (
    const c_qualifierst &a,
    const c_qualifierst &b)
  {
    return !(a==b);
  }
  
  c_qualifierst &operator += (
    const c_qualifierst &b)
  {
    is_constant|=b.is_constant;
    is_volatile|=b.is_volatile;
    is_restricted|=b.is_restricted;
    is_ptr32|=b.is_ptr32;
    is_ptr64|=b.is_ptr64;
    is_transparent_union|=b.is_transparent_union;
    return *this;
  }
  
  friend unsigned count(const c_qualifierst &q)
  {
    return q.is_constant+q.is_volatile+q.is_restricted+
           q.is_ptr32+q.is_ptr64;
  }
};

std::ostream &operator << (std::ostream &, const c_qualifierst &);

#endif
