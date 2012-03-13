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

  bool is_static()       const { return get_bool(ID_static); }
  bool is_extern()       const { return get_bool(ID_extern); }
  bool is_auto()         const { return get_bool(ID_auto); }
  bool is_register()     const { return get_bool(ID_register); }
  bool is_mutable()      const { return get_bool(ID_mutable); }
  bool is_thread_local() const { return get_bool(ID_thread_local); }
  bool is_asm()          const { return get_bool(ID_asm); }

  void set_static      () { set(ID_static, true); }
  void set_extern      () { set(ID_extern, true); }
  void set_auto        () { set(ID_auto, true); }
  void set_register    () { set(ID_register, true); }
  void set_mutable     () { set(ID_mutable, true); }
  void set_thread_local() { set(ID_thread_local, true); }
  void set_asm         () { set(ID_asm, true); }

  bool is_empty() const
  {
    return !is_static() && !is_extern() && !is_auto() &&
           !is_register() && !is_mutable() && !is_thread_local() &&
           !is_asm();
  }
};

#endif
