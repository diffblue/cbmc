/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "std_types.h"
#include "std_expr.h"
#include "rename_symbol.h"

/*******************************************************************\

Function: rename_symbolt::rename_symbolt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

rename_symbolt::rename_symbolt()
{
}

/*******************************************************************\

Function: rename_symbolt::~rename_symbolt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

rename_symbolt::~rename_symbolt()
{
}

/*******************************************************************\

Function: rename_symbolt::insert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rename_symbolt::insert(
  const symbol_exprt &old_expr,
  const symbol_exprt &new_expr)
{
  insert_expr(old_expr.get_identifier(), new_expr.get_identifier());
}

/*******************************************************************\

Function: rename_symbolt::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool rename_symbolt::rename(exprt &dest) const
{
  bool result=true;

  // first look at type

  if(have_to_rename(dest.type()))
    if(!rename(dest.type()))
      result=false;
      
  // now do expression itself

  if(!have_to_rename(dest))
    return result;

  if(dest.id()==ID_symbol)
  {
    expr_mapt::const_iterator it=
      expr_map.find(to_symbol_expr(dest).get_identifier());

    if(it!=expr_map.end())
    {
      to_symbol_expr(dest).set_identifier(it->second);
      return false;
    }
  }

  Forall_operands(it, dest)
    if(!rename(*it))
      result=false;

  const irept &c_sizeof_type=dest.find(ID_C_c_sizeof_type);

  if(c_sizeof_type.is_not_nil() &&
     !rename(static_cast<typet&>(dest.add(ID_C_c_sizeof_type))))
    result=false;

  const irept &va_arg_type=dest.find(ID_C_va_arg_type);

  if(va_arg_type.is_not_nil() &&
     !rename(static_cast<typet&>(dest.add(ID_C_va_arg_type))))
    result=false;

  return result;
}

/*******************************************************************\

Function: rename_symbolt::have_to_rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool rename_symbolt::have_to_rename(const exprt &dest) const
{
  // first look at type

  if(have_to_rename(dest.type()))
    return true;
      
  // now do expression itself

  if(dest.id()==ID_symbol)
    return expr_map.find(dest.get(ID_identifier))!=expr_map.end();

  forall_operands(it, dest)
    if(have_to_rename(*it))
      return true;

  const irept &c_sizeof_type=dest.find(ID_C_c_sizeof_type);

  if(c_sizeof_type.is_not_nil())
    if(have_to_rename(static_cast<const typet &>(c_sizeof_type)))
      return true;

  const irept &va_arg_type=dest.find(ID_C_va_arg_type);

  if(va_arg_type.is_not_nil())
    if(have_to_rename(static_cast<const typet &>(va_arg_type)))
      return true;

  return false;
}

/*******************************************************************\

Function: rename_symbolt::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool rename_symbolt::rename(typet &dest) const
{
  if(!have_to_rename(dest))
    return true;

  bool result=true;

  if(dest.has_subtype())
    if(!rename(dest.subtype()))
      result=false;

  Forall_subtypes(it, dest)
    if(!rename(*it))
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
      if(!rename(*it))
        result=false;
  } 
  else if(dest.id()==ID_code)
  {
    code_typet &code_type=to_code_type(dest);
    rename(code_type.return_type());
    code_typet::parameterst &parameters=code_type.parameters();

    for(code_typet::parameterst::iterator it = parameters.begin();
        it!=parameters.end();
        it++)
    {
      if(!rename(it->type()))
        result=false;

      expr_mapt::const_iterator e_it=
        expr_map.find(it->get_identifier());

      if(e_it!=expr_map.end())
      {
        it->set_identifier(e_it->second);
        result=false;
      }
    }
  }
  else if(dest.id()==ID_symbol)
  {
    type_mapt::const_iterator it=
      type_map.find(to_symbol_type(dest).get_identifier());

    if(it!=type_map.end())
    {
      to_symbol_type(dest).set_identifier(it->second);
      result=false;
    }
  }
  else if(dest.id()==ID_array)
  {
    array_typet &array_type=to_array_type(dest);
    if(!rename(array_type.size()))
      result=false;
  }

  return result;
}

/*******************************************************************\

Function: rename_symbolt::have_to_rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool rename_symbolt::have_to_rename(const typet &dest) const
{
  if(dest.has_subtype())
    if(have_to_rename(dest.subtype()))
      return true;

  forall_subtypes(it, dest)
    if(have_to_rename(*it))
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
      if(have_to_rename(*it))
        return true;
  } 
  else if(dest.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(dest);
    if(have_to_rename(code_type.return_type()))
      return true;
      
    const code_typet::parameterst &parameters=code_type.parameters();

    for(code_typet::parameterst::const_iterator
        it=parameters.begin();
        it!=parameters.end();
        it++)
    {
      if(have_to_rename(it->type()))
        return true;

      if(expr_map.find(it->get_identifier())!=expr_map.end())
        return true;
    }
  }
  else if(dest.id()==ID_symbol)
    return type_map.find(dest.get(ID_identifier))!=type_map.end();
  else if(dest.id()==ID_array)
    return have_to_rename(to_array_type(dest).size());

  return false;
}

