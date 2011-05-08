/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CPP_CLASS_TYPE_H
#define CPROVER_CPP_CLASS_TYPE_H

#include <std_types.h>

// used for C++ structs and classes

class class_typet:public struct_union_typet
{
public:
  inline class_typet():struct_union_typet(ID_struct)
  {
  }
  
  inline bool is_class() const
  {
    return get_bool(ID_C_class);    
  }
  
  inline irep_idt default_access() const
  {
    return is_class()?ID_private:ID_public;
  }

  inline const irept::subt &bases() const  
  {
    return find(ID_bases).get_sub();
  }
  
  bool has_base(const irep_idt &id) const
  {
    const irept::subt &b=bases();
    forall_irep(it, b)
    {
      assert(it->id()==ID_base);
      const irept &type=it->find(ID_type);
      assert(type.id()==ID_symbol);
      if(type.get(ID_identifier)==id) return true;
    }
    
    return false;
  }
};

extern inline const class_typet &to_class_type(const typet &type)
{
  assert(type.id()==ID_struct);
  return static_cast<const class_typet &>(type);
}

extern inline class_typet &to_class_type(typet &type)
{
  assert(type.id()==ID_struct);
  return static_cast<class_typet &>(type);
}

#endif
