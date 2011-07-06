/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <std_types.h>
#include <std_expr.h>

#include "anonymous_member.h"

/*******************************************************************\

Function: make_member_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static exprt make_member_expr(
  const exprt &struct_union,
  const struct_union_typet::componentt &component,
  const namespacet &ns)
{
  member_exprt result(
    struct_union, component.get_name(), component.type());

  if(struct_union.get_bool(ID_C_lvalue))
    result.set(ID_C_lvalue, true);

  // todo: should to typedef chains properly    
  const typet &type=
    ns.follow(struct_union.type());

  if(result.get_bool(ID_C_constant) ||
     type.get_bool(ID_C_constant) ||
     struct_union.type().get_bool(ID_C_constant))
    result.set(ID_C_constant, true);
    
  return result;
}

/*******************************************************************\

Function: get_component_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt get_component_rec(
  const exprt &struct_union,
  const irep_idt &component_name,
  const namespacet &ns)
{
  const struct_union_typet &struct_union_type=
    to_struct_union_type(ns.follow(struct_union.type()));

  const struct_union_typet::componentst &components=
    struct_union_type.components();

  for(struct_union_typet::componentst::const_iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    const typet &type=ns.follow(it->type());
  
    if(it->get_name()==component_name)
    {
      return make_member_expr(struct_union, *it, ns);
    }
    else if(it->get_anonymous() &&
            (type.id()==ID_struct || type.id()==ID_union))
    {
      exprt tmp=make_member_expr(struct_union, *it, ns);
      exprt result=get_component_rec(tmp, component_name, ns);
      if(result.is_not_nil()) return result;
    }
  }
  
  return nil_exprt();
}

/*******************************************************************\

Function: has_component_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool has_component_rec(
  const typet &type,
  const irep_idt &component_name,
  const namespacet &ns)
{
  const struct_union_typet &struct_union_type=
    to_struct_union_type(ns.follow(type));

  const struct_union_typet::componentst &components=
    struct_union_type.components();

  for(struct_union_typet::componentst::const_iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    if(it->get_name()==component_name)
    {
      return true;
    }
    else if(it->get_anonymous())
    {
      if(has_component_rec(it->type(), component_name, ns))
        return true;
    }
  }
  
  return false;
}
