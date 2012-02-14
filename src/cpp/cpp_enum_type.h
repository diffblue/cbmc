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
  inline cpp_enum_typet():typet(ID_c_enum)
  {
    set(ID_width, config.ansi_c.int_width);
  }
  
  inline const cpp_namet &tag() const
  {
    return static_cast<const cpp_namet &>(find(ID_tag));
  }
  
  inline bool has_tag() const
  {
    return find(ID_tag).is_not_nil();
  }
  
  inline cpp_namet &tag()
  {
    return static_cast<cpp_namet &>(add(ID_tag));
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
