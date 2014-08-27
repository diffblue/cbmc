/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "std_types.h"
#include "std_expr.h"
#include "replace_symbol.h"

/*******************************************************************\

Function: replace_symbolt::replace_symbolt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

replace_symbolt::replace_symbolt()
{
}

/*******************************************************************\

Function: replace_symbolt::~replace_symbolt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

replace_symbolt::~replace_symbolt()
{
}

/*******************************************************************\

Function: replace_symbolt::insert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void replace_symbolt::insert(
  const symbol_exprt &old_expr,
  const exprt &new_expr)
{
  expr_map.insert(std::pair<irep_idt, exprt>(
    old_expr.get_identifier(), new_expr));
}

/*******************************************************************\

Function: replace_symbolt::replace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool replace_symbolt::replace(exprt &dest) const
{
  bool result=true;

  // first look at type

  if(have_to_replace(dest.type()))
    if(!replace(dest.type()))
      result=false;
      
  // now do expression itself

  if(!have_to_replace(dest))
    return result;

  if(dest.id()==ID_symbol)
  {
    expr_mapt::const_iterator it=
      expr_map.find(dest.get(ID_identifier));

    if(it!=expr_map.end())
    {
      dest=it->second;
      return false;
    }
  }

  Forall_operands(it, dest)
    if(!replace(*it))
      result=false;

  const irept &c_sizeof_type=dest.find(ID_C_c_sizeof_type);

  if(c_sizeof_type.is_not_nil() &&
     !replace(static_cast<typet&>(dest.add(ID_C_c_sizeof_type))))
    result=false;

  const irept &va_arg_type=dest.find(ID_C_va_arg_type);

  if(va_arg_type.is_not_nil() &&
     !replace(static_cast<typet&>(dest.add(ID_C_va_arg_type))))
    result=false;

  return result;
}

/*******************************************************************\

Function: replace_symbolt::have_to_replace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool replace_symbolt::have_to_replace(const exprt &dest) const
{
  // first look at type

  if(have_to_replace(dest.type()))
    return true;
      
  // now do expression itself

  if(dest.id()==ID_symbol)
    return expr_map.find(dest.get(ID_identifier))!=expr_map.end();

  forall_operands(it, dest)
    if(have_to_replace(*it))
      return true;

  const irept &c_sizeof_type=dest.find(ID_C_c_sizeof_type);

  if(c_sizeof_type.is_not_nil())
    if(have_to_replace(static_cast<const typet &>(c_sizeof_type)))
      return true;

  const irept &va_arg_type=dest.find(ID_C_va_arg_type);

  if(va_arg_type.is_not_nil())
    if(have_to_replace(static_cast<const typet &>(va_arg_type)))
      return true;

  return false;
}

/*******************************************************************\

Function: replace_symbolt::replace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool replace_symbolt::replace(typet &dest) const
{
  if(!have_to_replace(dest))
    return true;

  bool result=true;

  if(dest.has_subtype())
    if(!replace(dest.subtype()))
      result=false;

  Forall_subtypes(it, dest)
    if(!replace(*it))
      result=false;
    
  if(dest.id()==ID_struct ||
     dest.id()==ID_union)
  {
    struct_union_typet &struct_union_type=to_struct_union_type(dest);    
    struct_union_typet::componentst &components=
      struct_union_type.components();

    for(struct_union_typet::componentst::iterator
        it=components.begin();
        it!=components.end();
        it++)
      if(!replace(*it))
        result=false;
  } 
  else if(dest.id()==ID_code)
  {
    code_typet &code_type=to_code_type(dest);
    replace(code_type.return_type());
    code_typet::parameterst &parameters=code_type.parameters();
    for(code_typet::parameterst::iterator it = parameters.begin();
        it!=parameters.end();
        it++)
      if(!replace(*it))
        result=false;
  }
  else if(dest.id()==ID_symbol)
  {
    type_mapt::const_iterator it=
      type_map.find(dest.get(ID_identifier));

    if(it!=type_map.end())
    {
      dest=it->second;
      result=false;
    }
  }
  else if(dest.id()==ID_array)
  {
    array_typet &array_type=to_array_type(dest);
    if(!replace(array_type.size()))
      result=false;
  }

  return result;
}

/*******************************************************************\

Function: replace_symbolt::have_to_replace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool replace_symbolt::have_to_replace(const typet &dest) const
{
  if(dest.has_subtype())
    if(have_to_replace(dest.subtype()))
      return true;

  forall_subtypes(it, dest)
    if(have_to_replace(*it))
      return true;
    
  if(dest.id()==ID_struct ||
     dest.id()==ID_union)
  {
    const struct_union_typet &struct_union_type=
      to_struct_union_type(dest);    

    const struct_union_typet::componentst &components=
      struct_union_type.components();

    for(struct_union_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
      if(have_to_replace(*it))
        return true;
  } 
  else if(dest.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(dest);
    if(have_to_replace(code_type.return_type()))
      return true;
      
    const code_typet::parameterst &parameters=code_type.parameters();

    for(code_typet::parameterst::const_iterator
        it=parameters.begin();
        it!=parameters.end();
        it++)
      if(have_to_replace(*it))
        return true;
  }
  else if(dest.id()==ID_symbol)
    return type_map.find(dest.get(ID_identifier))!=type_map.end();
  else if(dest.id()==ID_array)
    return have_to_replace(to_array_type(dest).size());

  return false;
}

