/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_DECLARATION_H
#define CPROVER_CPP_DECLARATION_H

#include <cassert>

#include "cpp_declarator.h"
#include "cpp_storage_spec.h"
#include "cpp_member_spec.h"
#include "cpp_template_type.h"
#include "cpp_template_args.h"

class cpp_declarationt:public exprt
{
public:
  typedef std::vector<cpp_declaratort> declaratorst;

  inline cpp_declarationt():exprt(ID_cpp_declaration)
  {
  }
  
  inline bool is_constructor() const
  {
    return type().id()==ID_constructor;
  }
  
  inline bool is_static_assert() const
  {
    return get_bool(ID_is_static_assert);
  }
  
  inline bool is_destructor() const
  {
    return type().id()==ID_destructor;
  }
  
  inline bool is_template() const
  {
    return get_bool(ID_is_template);
  }
  
  inline bool is_class_template() const
  {
    return is_template() &&
           type().id()==ID_struct &&
           declarators().empty();
  }
  
  inline const declaratorst &declarators() const
  {
    return (const declaratorst &)operands();
  }

  inline declaratorst &declarators()
  {
    return (declaratorst &)operands();
  }
  
  inline const cpp_storage_spect &storage_spec() const
  {
    return static_cast<const cpp_storage_spect &>(
      find(ID_storage_spec));
  }

  inline cpp_storage_spect &storage_spec()
  {
    return static_cast<cpp_storage_spect &>(
      add(ID_storage_spec));
  }

  inline const cpp_member_spect &member_spec() const
  {
    return static_cast<const cpp_member_spect &>(
      find(ID_member_spec));
  }

  inline cpp_member_spect &member_spec()
  {
    return static_cast<cpp_member_spect &>(
      add(ID_member_spec));
  }

  inline template_typet &template_type()
  {
    return static_cast<template_typet &>(add(ID_template_type));
  }

  inline const template_typet &template_type() const
  {
    return static_cast<const template_typet &>(find(ID_template_type));
  }

  inline cpp_template_args_non_tct &partial_specialization_args()
  {
    return static_cast<cpp_template_args_non_tct &>(add("partial_specialization_args"));
  }

  inline const cpp_template_args_non_tct &partial_specialization_args() const
  {
    return static_cast<const cpp_template_args_non_tct &>(find("partial_specialization_args"));
  }

  inline void set_specialization_of(const irep_idt &id)
  {
    set("specialization_of", id);
  }

  inline irep_idt get_specialization_of() const
  {
    return get("specialization_of");
  }
  
  bool is_typedef() const
  {
    const typet &t=type();
  
    return t.id()==ID_merged_type &&
           t.subtypes().size()>=2 &&
           t.subtypes()[0].id()==ID_typedef;
  }

  void output(std::ostream &out) const;

  // for assigning a tag for struct/union in the type based on
  // the name of the first declarator
  void name_anon_struct_union();
};

extern inline cpp_declarationt &to_cpp_declaration(irept &irep)
{
  assert(irep.id()==ID_cpp_declaration);
  return static_cast<cpp_declarationt &>(irep);
}

extern inline const cpp_declarationt &to_cpp_declaration(const irept &irep)
{
  assert(irep.id()==ID_cpp_declaration);
  return static_cast<const cpp_declarationt &>(irep);
}

#endif
