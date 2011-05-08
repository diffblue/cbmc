/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_CPP_MEMBER_SPEC_H
#define CPROVER_CPP_CPP_MEMBER_SPEC_H

#include "location.h"

class cpp_member_spect:public irept
{
public:
  cpp_member_spect():irept(ID_cpp_member_spec)
  {
  }

  bool is_virtual()  const { return get_bool(ID_virtual); }
  bool is_inline()   const { return get_bool(ID_inline); }
  bool is_friend()   const { return get_bool(ID_friend); }
  bool is_explicit() const { return get_bool(ID_explicit); }

  void set_virtual(bool value)  { set(ID_virtual, value); }
  void set_inline(bool value)   { set(ID_inline, value); }
  void set_friend(bool value)   { set(ID_friend, value); }
  void set_explicit(bool value) { set(ID_explicit, value); }
  
  bool is_empty() const
  {
    return !is_virtual() &&
           !is_inline() &&
           !is_friend() &&
           !is_explicit();
  }
};

#endif
