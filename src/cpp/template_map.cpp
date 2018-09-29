/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "template_map.h"

#include <ostream>

#include <util/invariant.h>
#include <util/std_expr.h>
#include <util/std_types.h>

void template_mapt::apply(typet &type) const
{
  if(type.id()==ID_array)
  {
    apply(type.subtype());
    apply(static_cast<exprt &>(type.add(ID_size)));
  }
  else if(type.id()==ID_pointer)
  {
    apply(type.subtype());
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
  {
    for(auto &c : to_struct_union_type(type).components())
    {
      typet &subtype = c.type();
      apply(subtype);
    }
  }
  else if(type.id() == ID_symbol_type)
  {
    type_mapt::const_iterator m_it =
      type_map.find(to_symbol_type(type).get_identifier());

    if(m_it!=type_map.end())
    {
      type=m_it->second;
      return;
    }
  }
  else if(type.id()==ID_code)
  {
    apply(to_code_type(type).return_type());

    irept::subt &parameters=type.add(ID_parameters).get_sub();

    Forall_irep(it, parameters)
    {
      if(it->id()==ID_parameter)
        apply(static_cast<typet &>(it->add(ID_type)));
    }
  }
  else if(type.id()==ID_merged_type)
  {
    Forall_subtypes(it, type)
      apply(*it);
  }
}

void template_mapt::apply(exprt &expr) const
{
  apply(expr.type());

  if(expr.id()==ID_symbol)
  {
    expr_mapt::const_iterator m_it =
      expr_map.find(to_symbol_expr(expr).get_identifier());

    if(m_it!=expr_map.end())
    {
      expr=m_it->second;
      return;
    }
  }

  Forall_operands(it, expr)
    apply(*it);
}

exprt template_mapt::lookup(const irep_idt &identifier) const
{
  type_mapt::const_iterator t_it=
    type_map.find(identifier);

  if(t_it!=type_map.end())
  {
    exprt e(ID_type);
    e.type()=t_it->second;
    return e;
  }

  expr_mapt::const_iterator e_it=
    expr_map.find(identifier);

  if(e_it!=expr_map.end())
    return e_it->second;

  return static_cast<const exprt &>(get_nil_irep());
}

typet template_mapt::lookup_type(const irep_idt &identifier) const
{
  type_mapt::const_iterator t_it=
    type_map.find(identifier);

  if(t_it!=type_map.end())
    return t_it->second;

  return static_cast<const typet &>(get_nil_irep());
}

exprt template_mapt::lookup_expr(const irep_idt &identifier) const
{
  expr_mapt::const_iterator e_it=
    expr_map.find(identifier);

  if(e_it!=expr_map.end())
    return e_it->second;

  return static_cast<const exprt &>(get_nil_irep());
}

void template_mapt::print(std::ostream &out) const
{
  for(const auto &mapping : type_map)
    out << mapping.first << " = " << mapping.second.pretty() << '\n';

  for(const auto &mapping : expr_map)
    out << mapping.first << " = " << mapping.second.pretty() << '\n';
}

void template_mapt::build(
  const template_typet &template_type,
  const cpp_template_args_tct &template_args)
{
  const template_typet::template_parameterst &template_parameters=
    template_type.template_parameters();

  cpp_template_args_tct::argumentst instance=
    template_args.arguments();

  template_typet::template_parameterst::const_iterator t_it=
    template_parameters.begin();

  if(instance.size()<template_parameters.size())
  {
    // check for default parameters
    for(std::size_t i=instance.size();
        i<template_parameters.size();
        i++)
    {
      const template_parametert &param=template_parameters[i];

      if(param.has_default_argument())
        instance.push_back(param.default_argument());
      else
        break;
    }
  }

  // these should have been typechecked before
  DATA_INVARIANT(
    instance.size() == template_parameters.size(),
    "template instantiation expected to match declaration");

  for(cpp_template_args_tct::argumentst::const_iterator
      i_it=instance.begin();
      i_it!=instance.end();
      i_it++, t_it++)
  {
    set(*t_it, *i_it);
  }
}

void template_mapt::set(
  const template_parametert &parameter,
  const exprt &value)
{
  if(parameter.id()==ID_type)
  {
    if(parameter.id()!=ID_type)
      UNREACHABLE; // typechecked before!

    typet tmp=value.type();

    irep_idt identifier=parameter.type().get(ID_identifier);
    type_map[identifier]=tmp;
  }
  else
  {
    // must be non-type

    if(value.id()==ID_type)
      UNREACHABLE; // typechecked before!

    irep_idt identifier=parameter.get(ID_identifier);
    expr_map[identifier]=value;
  }
}

void template_mapt::build_unassigned(
  const template_typet &template_type)
{
  for(const auto &t : template_type.template_parameters())
  {
    if(t.id()==ID_type)
    {
      typet tmp(ID_unassigned);
      tmp.set(ID_identifier, t.type().get(ID_identifier));
      tmp.add_source_location()=t.source_location();
      type_map[t.type().get(ID_identifier)]=tmp;
    }
    else
    {
      exprt tmp(ID_unassigned, t.type());
      tmp.set(ID_identifier, t.get(ID_identifier));
      tmp.add_source_location()=t.source_location();
      expr_map[t.get(ID_identifier)]=tmp;
    }
  }
}

cpp_template_args_tct template_mapt::build_template_args(
  const template_typet &template_type) const
{
  const template_typet::template_parameterst &template_parameters=
    template_type.template_parameters();

  cpp_template_args_tct template_args;
  template_args.arguments().resize(template_parameters.size());

  for(std::size_t i=0; i<template_parameters.size(); i++)
  {
    const template_parametert &t=template_parameters[i];

    if(t.id()==ID_type)
    {
      template_args.arguments()[i]=
        exprt(ID_type, lookup_type(t.type().get(ID_identifier)));
    }
    else
    {
      template_args.arguments()[i]=
        lookup_expr(t.get(ID_identifier));
    }
  }

  return template_args;
}
