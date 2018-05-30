/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/


#ifndef CPROVER_CPP_CPP_STORAGE_SPEC_H
#define CPROVER_CPP_CPP_STORAGE_SPEC_H

#include <util/type.h>

class cpp_storage_spect:public irept
{
public:
  cpp_storage_spect():irept(ID_cpp_storage_spec)
  {
  }

  explicit cpp_storage_spect(const typet &type)
  {
    read(type);
  }

  source_locationt &location()
  {
    return static_cast<source_locationt &>(add(ID_C_source_location));
  }

  const source_locationt &location() const
  {
    return static_cast<const source_locationt &>(find(ID_C_source_location));
  }

  bool is_static()       const { return get_bool(ID_static); }
  bool is_extern()       const { return get_bool(ID_extern); }
  bool is_auto()         const { return get_bool(ID_auto); }
  bool is_register()     const { return get_bool(ID_register); }
  bool is_mutable()      const { return get_bool(ID_mutable); }
  bool is_thread_local() const { return get_bool(ID_thread_local); }
  bool is_asm()          const { return get_bool(ID_asm); }
  bool is_weak() const
  {
    return get_bool(ID_weak);
  }

  void set_static()       { set(ID_static, true); }
  void set_extern()       { set(ID_extern, true); }
  void set_auto()         { set(ID_auto, true); }
  void set_register()     { set(ID_register, true); }
  void set_mutable()      { set(ID_mutable, true); }
  void set_thread_local() { set(ID_thread_local, true); }
  void set_asm()          { set(ID_asm, true); }
  void set_weak()
  {
    set(ID_weak, true);
  }

  bool is_empty() const
  {
    return !is_static() && !is_extern() && !is_auto() && !is_register() &&
           !is_mutable() && !is_thread_local() && !is_asm() && !is_weak();
  }

  cpp_storage_spect &operator|=(const cpp_storage_spect &other)
  {
    if(other.is_static())
      set_static();
    if(other.is_extern())
      set_extern();
    if(other.is_auto())
      set_auto();
    if(other.is_register())
      set_register();
    if(other.is_mutable())
      set_mutable();
    if(other.is_thread_local())
      set_thread_local();
    if(other.is_asm())
      set_asm();
    if(other.is_weak())
      set_weak();

    return *this;
  }

private:
  void read(const typet &type);
};

#endif // CPROVER_CPP_CPP_STORAGE_SPEC_H
