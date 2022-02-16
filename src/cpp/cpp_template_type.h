/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/


#ifndef CPROVER_CPP_CPP_TEMPLATE_TYPE_H
#define CPROVER_CPP_CPP_TEMPLATE_TYPE_H

#include <util/invariant.h>
#include <util/type.h>

#include "cpp_template_parameter.h"

class template_typet:public typet
{
public:
  template_typet():typet(ID_template)
  {
  }

  typedef std::vector<template_parametert> template_parameterst;

  template_parameterst &template_parameters()
  {
    return (template_parameterst &)add(ID_template_parameters).get_sub();
  }

  const template_parameterst &template_parameters() const
  {
    return (const template_parameterst &)find(ID_template_parameters).get_sub();
  }

  using typet::subtype;
};

inline template_typet &to_template_type(typet &type)
{
  PRECONDITION(type.id() == ID_template);
  return static_cast<template_typet &>(type);
}

inline const template_typet &to_template_type(const typet &type)
{
  PRECONDITION(type.id() == ID_template);
  return static_cast<const template_typet &>(type);
}

inline const typet &template_subtype(const typet &type)
{
  if(type.id()==ID_template)
    return to_type_with_subtype(type).subtype();

  return type;
}

inline typet &template_subtype(typet &type)
{
  if(type.id()==ID_template)
    return type.subtype();

  return type;
}

#endif // CPROVER_CPP_CPP_TEMPLATE_TYPE_H
