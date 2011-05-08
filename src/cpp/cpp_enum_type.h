/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_ENUM_TYPE_H
#define CPROVER_CPP_ENUM_TYPE_H

#include <assert.h>

#include <config.h>
#include <type.h>

class cpp_enum_typet:public typet
{
public:
  cpp_enum_typet():typet(ID_c_enum)
  {
    set(ID_width, config.ansi_c.int_width);
  }
  
  const irep_idt &get_name() const
  {
    return get(ID_name);
  }
  
  void set_name(const irep_idt &name)
  {
    set(ID_name, name);
  }

  const irept &body() const
  {
    return find(ID_body);
  }

  irept &body()
  {
    return add(ID_body);
  }
  
  bool has_body() const
  {
    return find(ID_body).is_not_nil();
  }

  bool get_tag_only_declaration() const
  {
    return get_bool(ID_C_tag_only_declaration);
  }
};

extern inline const cpp_enum_typet &to_cpp_enum_type(const irept &irep)
{
  assert(irep.id()==ID_c_enum);
  return static_cast<const cpp_enum_typet &>(irep);
}

extern inline cpp_enum_typet &to_cpp_enum_type(irept &irep)
{
  assert(irep.id()==ID_c_enum);
  return static_cast<cpp_enum_typet &>(irep);
}

#endif
