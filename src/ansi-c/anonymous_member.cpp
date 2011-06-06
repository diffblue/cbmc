/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <std_types.h>
#include <std_expr.h>

#include "anonymous_member.h"

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
    if(it->get_name()==component_name)
    {
      return member_exprt(struct_union, component_name);
    }
    else if(it->get_anonymous())
    {
      exprt tmp1=member_exprt(struct_union, it->get_name(), it->type());
      exprt tmp2=get_component_rec(tmp1, component_name, ns);
      if(tmp2.is_not_nil()) return tmp2;
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
