/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_TEMPLATE_TYPE_H
#define CPROVER_CPP_TEMPLATE_TYPE_H

#include <type.h>

#include "cpp_template_parameter.h"

class template_parametert:public exprt
{
public:
  inline exprt &default_parameter()
  {
    return static_cast<exprt &>(add("#default"));
  }

  inline const exprt &default_parameter() const
  {
    return static_cast<const exprt &>(find("#default"));
  }
};

class template_typet:public typet
{
public:
  inline template_typet():typet(ID_template)
  {
  }

  typedef std::vector<template_parametert> parameterst;

  inline parameterst &parameters()
  {
    // todo: will change to 'parameters'
    return (parameterst &)add(ID_arguments).get_sub();
  }

  inline const parameterst &parameters() const
  {
    // todo: will change to 'parameters'
    return (const parameterst &)find(ID_arguments).get_sub();
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
