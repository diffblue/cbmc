/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_DECLARATION_H
#define CPROVER_CPP_CPP_DECLARATION_H

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

  cpp_declarationt():exprt(ID_cpp_declaration)
  {
  }

  bool is_empty() const
  {
    return type().is_nil() && !has_operands();
  }

  bool is_constructor() const
  {
    return type().id()==ID_constructor;
  }

  bool is_static_assert() const
  {
    return get_bool(ID_is_static_assert);
  }

  bool is_destructor() const
  {
    return type().id()==ID_destructor;
  }

  bool is_template() const
  {
    return get_bool(ID_is_template);
  }

  bool is_class_template() const
  {
    return is_template() &&
           type().id()==ID_struct &&
           declarators().empty();
  }

  const declaratorst &declarators() const
  {
    return (const declaratorst &)operands();
  }

  declaratorst &declarators()
  {
    return (declaratorst &)operands();
  }

  const cpp_storage_spect &storage_spec() const
  {
    return static_cast<const cpp_storage_spect &>(
      find(ID_storage_spec));
  }

  cpp_storage_spect &storage_spec()
  {
    return static_cast<cpp_storage_spect &>(
      add(ID_storage_spec));
  }

  const cpp_member_spect &member_spec() const
  {
    return static_cast<const cpp_member_spect &>(
      find(ID_member_spec));
  }

  cpp_member_spect &member_spec()
  {
    return static_cast<cpp_member_spect &>(
      add(ID_member_spec));
  }

  template_typet &template_type()
  {
    return static_cast<template_typet &>(add(ID_template_type));
  }

  const template_typet &template_type() const
  {
    return static_cast<const template_typet &>(find(ID_template_type));
  }

  cpp_template_args_non_tct &partial_specialization_args()
  {
    return static_cast<cpp_template_args_non_tct &>(
      add(ID_partial_specialization_args));
  }

  const cpp_template_args_non_tct &partial_specialization_args() const
  {
    return static_cast<const cpp_template_args_non_tct &>(
      find(ID_partial_specialization_args));
  }

  void set_specialization_of(const irep_idt &id)
  {
    set(ID_specialization_of, id);
  }

  irep_idt get_specialization_of() const
  {
    return get(ID_specialization_of);
  }

  void set_is_typedef()
  {
    set(ID_is_typedef, true);
  }

  bool is_typedef() const
  {
    return get_bool(ID_is_typedef);
  }

  void output(std::ostream &out) const;

  // for assigning a tag for struct/union in the type based on
  // the name of the first declarator
  void name_anon_struct_union() { name_anon_struct_union(type()); }
  void name_anon_struct_union(typet &dest);
};

inline cpp_declarationt &to_cpp_declaration(irept &irep)
{
  assert(irep.id()==ID_cpp_declaration);
  return static_cast<cpp_declarationt &>(irep);
}

inline const cpp_declarationt &to_cpp_declaration(const irept &irep)
{
  assert(irep.id()==ID_cpp_declaration);
  return static_cast<const cpp_declarationt &>(irep);
}

#endif // CPROVER_CPP_CPP_DECLARATION_H
