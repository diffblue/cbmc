/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include "template_map.h"

/*******************************************************************\

Function: template_mapt::apply

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    irept::subt &components=type.add(ID_components).get_sub();

    Forall_irep(it, components)
    {
      typet &subtype=static_cast<typet &>(it->add(ID_type));
      apply(subtype);
    }
  }
  else if(type.id()==ID_symbol)
  {
    type_mapt::const_iterator m_it=
      type_map.find(type.get(ID_identifier));

    if(m_it!=type_map.end())
    {
      type=m_it->second;
      return;
    }
  }
  else if(type.id()==ID_code)
  {
    apply(static_cast<typet &>(type.add(ID_return_type)));

    irept::subt &arguments=type.add(ID_arguments).get_sub();

    Forall_irep(it, arguments)
    {
      if(it->id()==ID_argument)
        apply(static_cast<typet &>(it->add(ID_type)));
    }
  }
  else if(type.id()==ID_merged_type)
  {
    Forall_subtypes(it, type)
      apply(*it);
  }
}

/*******************************************************************\

Function: template_mapt::apply

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_mapt::apply(exprt &expr) const
{
  apply(expr.type());

  if(expr.id()==ID_symbol)
  {
    expr_mapt::const_iterator m_it=
      expr_map.find(expr.get(ID_identifier));

    if(m_it!=expr_map.end())
    {
      expr=m_it->second;
      return;
    }
  }

  Forall_operands(it, expr)
    apply(*it);
}

/*******************************************************************\

Function: template_mapt::lookup

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: template_mapt::lookup_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet template_mapt::lookup_type(const irep_idt &identifier) const
{
  type_mapt::const_iterator t_it=
    type_map.find(identifier);

  if(t_it!=type_map.end())
    return t_it->second;

  return static_cast<const typet &>(get_nil_irep());
}

/*******************************************************************\

Function: template_mapt::lookup_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt template_mapt::lookup_expr(const irep_idt &identifier) const
{
  expr_mapt::const_iterator e_it=
    expr_map.find(identifier);

  if(e_it!=expr_map.end())
    return e_it->second;

  return static_cast<const exprt &>(get_nil_irep());
}

/*******************************************************************\

Function: template_mapt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_mapt::print(std::ostream &out) const
{
  for(type_mapt::const_iterator it=type_map.begin();
      it!=type_map.end();
      it++)
    out << it->first << " = " << it->second.pretty() << std::endl;

  for(expr_mapt::const_iterator it=expr_map.begin();
      it!=expr_map.end();
      it++)
    out << it->first << " = " << it->second.pretty() << std::endl;
}

/*******************************************************************\

Function: template_mapt::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_mapt::build(
  const template_typet &template_type,
  const cpp_template_args_tct &template_args)
{
  const template_typet::parameterst &template_parameters=
    template_type.parameters();

  cpp_template_args_tct::argumentst instance=
    template_args.arguments();

  template_typet::parameterst::const_iterator t_it=
    template_parameters.begin();

  if(instance.size()<template_parameters.size())
  {
    // check for default parameters
    for(unsigned i=instance.size();
        i<template_parameters.size();
        i++)
    {
      const template_parametert &param=template_parameters[i];

      if(param.has_default_parameter())
        instance.push_back(param.default_parameter());
      else
        break;
    }
  }

  // these should have been typechecked before
  assert(instance.size()==template_parameters.size());

  for(cpp_template_args_tct::argumentst::const_iterator
      i_it=instance.begin();
      i_it!=instance.end();
      i_it++, t_it++)
  {
    assert(t_it!=template_parameters.end());
    set(*t_it, *i_it);
  }
}

/*******************************************************************\

Function: template_mapt::set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_mapt::set(
  const template_parametert &parameter,
  const exprt &value)
{
  if(parameter.id()==ID_type)
  {
    if(parameter.id()!=ID_type)
      assert(false); // typechecked before!

    typet tmp=value.type();

    irep_idt identifier=parameter.type().get(ID_identifier);
    type_map[identifier]=tmp;
  }
  else
  {
    // must be non-type
  
    if(value.id()==ID_type)
      assert(false); // typechecked before!

    irep_idt identifier=parameter.get(ID_identifier);
    expr_map[identifier]=value;
  }    
}

/*******************************************************************\

Function: template_mapt::build_unassigned

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_mapt::build_unassigned(
  const template_typet &template_type)
{
  const template_typet::parameterst &template_parameters=
    template_type.parameters();

  for(template_typet::parameterst::const_iterator
      t_it=template_parameters.begin();
      t_it!=template_parameters.end();
      t_it++)
  {
    const exprt &t=*t_it;
    
    if(t.id()==ID_type)
    {
      typet tmp(ID_unassigned);
      tmp.set(ID_identifier, t.type().get(ID_identifier));
      tmp.location()=t.location();
      type_map[t.type().get(ID_identifier)]=tmp;
    }
    else
    {
      exprt tmp(ID_unassigned, t.type());
      tmp.set(ID_identifier, t.get(ID_identifier));
      tmp.location()=t.location();
      expr_map[t.get(ID_identifier)]=tmp;
    }    
  }
}

/*******************************************************************\

Function: template_mapt::build_template_args

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cpp_template_args_tct template_mapt::build_template_args(
  const template_typet &template_type) const
{
  const template_typet::parameterst &template_parameters=
    template_type.parameters();

  cpp_template_args_tct template_args;
  template_args.arguments().resize(template_parameters.size());
  
  for(unsigned i=0; i<template_parameters.size(); i++)
  {
    const exprt &t=template_parameters[i];
    
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

