/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

#include "cpp_storage_spec.h"

void cpp_storage_spect::read(const typet &type)
{
  if(type.id() == ID_merged_type || type.id() == ID_function_type)
  {
    forall_subtypes(it, type)
      read(*it);
  }
  else if(type.id() == ID_static)
    set_static();
  else if(type.id() == ID_extern)
    set_extern();
  else if(type.id() == ID_auto)
    set_auto();
  else if(type.id() == ID_register)
    set_register();
  else if(type.id() == ID_mutable)
    set_mutable();
  else if(type.id() == ID_thread_local)
    set_thread_local();
  else if(type.id() == ID_asm)
    set_asm();
  else if(type.id() == ID_weak)
    set_weak();
}
