/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_TEMPLATE_TYPE_H
#define CPROVER_CPP_TEMPLATE_TYPE_H

#include <util/type.h>
#include <util/expr.h>

#include "cpp_template_parameter.h"

class template_typet:public typet
{
public:
  inline template_typet():typet(ID_template)
  {
  }

  typedef std::vector<template_parametert> template_parameterst;

  inline template_parameterst &template_parameters()
  {
    return (template_parameterst &)add(ID_template_parameters).get_sub();
  }

  inline const template_parameterst &template_parameters() const
  {
    return (const template_parameterst &)find(ID_template_parameters).get_sub();
  }
};

inline template_typet &to_template_type(typet &type)
{
  assert(type.id()==ID_template);
  return static_cast<template_typet &>(type);
}

inline const template_typet &to_template_type(const typet &type)
{
  assert(type.id()==ID_template);
  return static_cast<const template_typet &>(type);
}

inline const typet &template_subtype(const typet &type)
{
  if(type.id()==ID_template)
    return type.subtype();

  return type;
}

inline typet &template_subtype(typet &type)
{
  if(type.id()==ID_template)
    return type.subtype();

  return type;
}

#endif
