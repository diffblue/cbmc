/*******************************************************************\

Module: Base Type Computation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <set>

#include "std_types.h"
#include "base_type.h"
#include "namespace.h"
#include "symbol.h"

/*******************************************************************\

Function: base_type_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void base_type_rec(
  typet &type, const namespacet &ns, std::set<irep_idt> &symb)
{
  if(type.id()==ID_symbol)
  {
    const symbolt *symbol;

    if(!ns.lookup(type.get(ID_identifier), symbol) &&
       symbol->is_type &&
       !symbol->type.is_nil())
    {
      type=symbol->type;
      base_type_rec(type, ns, symb); // recursive call
      return;
    }
  }
  else if(type.id()==ID_subtype)
  {
    typet tmp;
    tmp.swap(type.subtype());
    type.swap(tmp);
  }
  else if(type.id()==ID_array)
  {
    base_type_rec(type.subtype(), ns, symb);
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
  {
    irept::subt &components=type.add(ID_components).get_sub();

    Forall_irep(it, components)
    {
      typet &subtype=static_cast<typet &>(it->add(ID_type));
      base_type_rec(subtype, ns, symb);
    }
  }
  else if(type.id()==ID_pointer)
  {
    typet &subtype=type.subtype();

    // we need to avoid running into an infinite loop
    if(subtype.id()==ID_symbol)
    {
      const irep_idt &id=to_symbol_type(subtype).get_identifier();

      if(symb.find(id)!=symb.end())
        return;
      
      symb.insert(id);

      base_type_rec(subtype, ns, symb);
      
      symb.erase(id);
    }
    else
      base_type_rec(subtype, ns, symb);
  }
}

/*******************************************************************\

Function: base_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void base_type(typet &type, const namespacet &ns)
{
  std::set<irep_idt> symb;
  base_type_rec(type, ns, symb);
}

/*******************************************************************\

Function: base_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void base_type(exprt &expr, const namespacet &ns)
{
  base_type(expr.type(), ns);

  Forall_operands(it, expr)
    base_type(*it, ns);
}

/*******************************************************************\

Function: base_type_eqt::base_type_eq_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool base_type_eqt::base_type_eq_rec(
  const typet &type1,
  const typet &type2)
{
  if(type1==type2)
    return true;
    
  #if 0
  std::cout << "T1: " << type1.pretty() << std::endl;
  std::cout << "T2: " << type2.pretty() << std::endl;
  #endif
  
  // loop avoidance
  if(type1.id()==ID_symbol &&
     type2.id()==ID_symbol)
  {
    // already in same set?
    if(identifiers.make_union(
         to_symbol_type(type1).get_identifier(),
         to_symbol_type(type2).get_identifier()))
      return true;
  }

  if(type1.id()==ID_symbol)
  {
    const symbolt &symbol=
      ns.lookup(to_symbol_type(type1).get_identifier());

    if(!symbol.is_type)
      return false;
    
    return base_type_eq_rec(symbol.type, type2);
  }

  if(type2.id()==ID_symbol)
  {
    const symbolt &symbol=
      ns.lookup(to_symbol_type(type2).get_identifier());

    if(!symbol.is_type)
      return false;

    return base_type_eq_rec(type1, symbol.type);
  }
  
  if(type1.id()!=type2.id())
    return false;

  if(type1.id()==ID_struct ||
     type1.id()==ID_union)
  {
    const struct_union_typet::componentst &components1=
      to_struct_union_type(type1).components();

    const struct_union_typet::componentst &components2=
      to_struct_union_type(type2).components();
      
    if(components1.size()!=components2.size())
      return false;

    for(unsigned i=0; i<components1.size(); i++)
    {
      const typet &subtype1=components1[i].type();
      const typet &subtype2=components2[i].type();
      if(!base_type_eq_rec(subtype1, subtype2)) return false;
      if(components1[i].get_name()!=components2[i].get_name()) return false;
    }
    
    return true;
  }
  else if(type1.id()==ID_incomplete_struct)
  {
    return true;
  }
  else if(type1.id()==ID_incomplete_union)
  {
    return true;
  }
  else if(type1.id()==ID_code)
  {
    const code_typet::argumentst &arguments1=
      to_code_type(type1).arguments();

    const code_typet::argumentst &arguments2=
      to_code_type(type2).arguments();
    
    if(arguments1.size()!=arguments2.size())
      return false;
      
    for(unsigned i=0; i<arguments1.size(); i++)
    {
      const typet &subtype1=arguments1[i].type();
      const typet &subtype2=arguments2[i].type();
      if(!base_type_eq_rec(subtype1, subtype2)) return false;
    }
    
    const typet &return_type1=to_code_type(type1).return_type();
    const typet &return_type2=to_code_type(type2).return_type();
    
    if(!base_type_eq_rec(return_type1, return_type2))
      return false;
    
    return true;
  }
  else if(type1.id()==ID_pointer)
  {
    return base_type_eq_rec(type1.subtype(), type2.subtype());
  }
  else if(type1.id()==ID_array)
  {
    if(!base_type_eq_rec(type1.subtype(), type2.subtype()))
      return false;

    if(to_array_type(type1).size()!=to_array_type(type2).size())
      return false;
      
    return true;
  }
  else if(type1.id()==ID_incomplete_array)
  {
    return base_type_eq_rec(type1.subtype(), type2.subtype());
  }

  // the below will go away
  typet tmp1(type1), tmp2(type2);

  base_type(tmp1, ns);
  base_type(tmp2, ns);

  return tmp1==tmp2;  
}

/*******************************************************************\

Function: base_type_eqt::base_type_eq_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool base_type_eqt::base_type_eq_rec(
  const exprt &expr1,
  const exprt &expr2)
{
  if(expr1.id()!=expr2.id())
    return false;
    
  if(!base_type_eq(expr1.type(), expr2.type()))
    return false;

  if(expr1.operands().size()!=expr2.operands().size())
    return false;
    
  for(unsigned i=0; i<expr1.operands().size(); i++)
    if(!base_type_eq(expr1.operands()[i], expr2.operands()[i]))
      return false;
  
  return true;
}

/*******************************************************************\

Function: base_type_eq

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool base_type_eq(
  const typet &type1,
  const typet &type2,
  const namespacet &ns)
{
  base_type_eqt base_type_eq(ns);
  return base_type_eq.base_type_eq(type1, type2);
}

/*******************************************************************\

Function: base_type_eq

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool base_type_eq(
  const exprt &expr1,
  const exprt &expr2,
  const namespacet &ns)
{
  base_type_eqt base_type_eq(ns);
  return base_type_eq.base_type_eq(expr1, expr2);
}
