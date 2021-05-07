/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_C_STORAGE_SPEC_H
#define CPROVER_ANSI_C_C_STORAGE_SPEC_H

#include <util/irep.h>

class typet;

class c_storage_spect
{
public:
  c_storage_spect()
  {
    clear();
  }

  explicit c_storage_spect(const typet &type)
  {
    clear();
    read(type);
  }

  void clear()
  {
    is_typedef=false;
    is_extern=false;
    is_thread_local=false;
    is_static=false;
    is_register=false;
    is_inline=false;
    is_weak=false;
    is_used = false;
    alias.clear();
    asm_label.clear();
    section.clear();
  }

  bool is_typedef, is_extern, is_static, is_register,
       is_inline, is_thread_local, is_weak, is_used;

  // __attribute__((alias("foo")))
  irep_idt alias;

  // GCC asm labels __asm__("foo") - these change the symbol name
  irep_idt asm_label;
  irep_idt section;

  bool operator==(const c_storage_spect &other) const
  {
    return is_typedef==other.is_typedef &&
           is_extern==other.is_extern &&
           is_static==other.is_static &&
           is_register==other.is_register &&
           is_thread_local==other.is_thread_local &&
           is_inline==other.is_inline &&
           is_weak==other.is_weak &&
           is_used == other.is_used &&
           alias==other.alias &&
           asm_label==other.asm_label &&
           section==other.section;
  }

  bool operator!=(const c_storage_spect &other) const
  {
    return !(*this==other);
  }

  c_storage_spect &operator|=(const c_storage_spect &other)
  {
    is_typedef      |=other.is_typedef;
    is_extern       |=other.is_extern;
    is_static       |=other.is_static;
    is_register     |=other.is_register;
    is_inline       |=other.is_inline;
    is_thread_local |=other.is_thread_local;
    is_weak         |=other.is_weak;
    is_used         |=other.is_used;
    if(alias.empty())
      alias=other.alias;
    if(asm_label.empty())
      asm_label=other.asm_label;
    if(section.empty())
      section=other.section;

    return *this;
  }

  void read(const typet &type);
};

#endif // CPROVER_ANSI_C_C_STORAGE_SPEC_H
