/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_CPP_STORAGE_SPEC_H
#define CPROVER_CPP_CPP_STORAGE_SPEC_H

#include <location.h>

class cpp_storage_spect:public irept
{
public:
  cpp_storage_spect():irept(ID_cpp_storage_spec)
  {
  }
  
  locationt &location()
  {
    return static_cast<locationt &>(add(ID_C_location));
  }

  const locationt &location() const
  {
    return static_cast<const locationt &>(find(ID_C_location));
  }

  bool is_static()   const { return get(ID_storage)==ID_static; }
  bool is_extern()   const { return get(ID_storage)==ID_extern; }
  bool is_auto()     const { return get(ID_storage)==ID_auto; }
  bool is_register() const { return get(ID_storage)==ID_register; }
  bool is_mutable()  const { return get(ID_storage)==ID_mutable; }

  void set_static  () { set(ID_storage, ID_static); }
  void set_extern  () { set(ID_storage, ID_extern); }
  void set_auto    () { set(ID_storage, ID_auto); }
  void set_register() { set(ID_storage, ID_register); }
  void set_mutable () { set(ID_storage, ID_mutable); }

  bool is_empty() const
  {
    return get(ID_storage)==irep_idt();
  }
};

#endif
