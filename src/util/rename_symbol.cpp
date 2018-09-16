/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "rename_symbol.h"

#include "expr_iterator.h"
#include "std_types.h"
#include "std_expr.h"

rename_symbolt::rename_symbolt()
{
}

rename_symbolt::~rename_symbolt()
{
}

void rename_symbolt::insert(
  const symbol_exprt &old_expr,
  const symbol_exprt &new_expr)
{
  insert_expr(old_expr.get_identifier(), new_expr.get_identifier());
}

bool rename_symbolt::rename(exprt &dest) const
{
  bool result=true;

  for(auto it = dest.depth_begin(), end = dest.depth_end(); it != end; ++it)
  {
    exprt * modifiable_expr = nullptr;

    // first look at type
    if(have_to_rename(it->type()))
    {
      modifiable_expr = &it.mutate();
      result &= rename(modifiable_expr->type());
    }

    // now do expression itself
    if(it->id()==ID_symbol)
    {
      expr_mapt::const_iterator entry =
        expr_map.find(to_symbol_expr(*it).get_identifier());

      if(entry != expr_map.end())
      {
        if(!modifiable_expr)
          modifiable_expr = &it.mutate();
        to_symbol_expr(*modifiable_expr).set_identifier(entry->second);
        result = false;
      }
    }

    const typet &c_sizeof_type =
      static_cast<const typet&>(it->find(ID_C_c_sizeof_type));
    if(c_sizeof_type.is_not_nil() && have_to_rename(c_sizeof_type))
    {
      if(!modifiable_expr)
        modifiable_expr = &it.mutate();
      result &=
        rename(static_cast<typet&>(modifiable_expr->add(ID_C_c_sizeof_type)));
    }

    const typet &va_arg_type =
      static_cast<const typet&>(it->find(ID_C_va_arg_type));
    if(va_arg_type.is_not_nil() && have_to_rename(va_arg_type))
    {
      if(!modifiable_expr)
        modifiable_expr = &it.mutate();
      result &=
        rename(static_cast<typet&>(modifiable_expr->add(ID_C_va_arg_type)));
    }
  }

  return result;
}

bool rename_symbolt::have_to_rename(const exprt &dest) const
{
  if(expr_map.empty() && type_map.empty())
    return false;

  // first look at type

  if(have_to_rename(dest.type()))
    return true;

  // now do expression itself

  if(dest.id()==ID_symbol)
  {
    const irep_idt &identifier = to_symbol_expr(dest).get_identifier();
    return expr_map.find(identifier) != expr_map.end();
  }

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

    for(auto &c : struct_union_type.components())
      if(!rename(c))
        result=false;
  }
  else if(dest.id()==ID_code)
  {
    code_typet &code_type=to_code_type(dest);
    rename(code_type.return_type());

    for(auto &p : code_type.parameters())
    {
      if(!rename(p.type()))
        result=false;

      expr_mapt::const_iterator e_it = expr_map.find(p.get_identifier());

      if(e_it!=expr_map.end())
      {
        p.set_identifier(e_it->second);
        result=false;
      }
    }
  }
  else if(dest.id() == ID_symbol_type)
  {
    type_mapt::const_iterator it=
      type_map.find(to_symbol_type(dest).get_identifier());

    if(it!=type_map.end())
    {
      to_symbol_type(dest).set_identifier(it->second);
      result=false;
    }
  }
  else if(dest.id()==ID_c_enum_tag ||
          dest.id()==ID_struct_tag ||
          dest.id()==ID_union_tag)
  {
    type_mapt::const_iterator it=
      type_map.find(to_tag_type(dest).get_identifier());

    if(it!=type_map.end())
    {
      to_tag_type(dest).set_identifier(it->second);
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

bool rename_symbolt::have_to_rename(const typet &dest) const
{
  if(expr_map.empty() && type_map.empty())
    return false;

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

    for(const auto &c : struct_union_type.components())
      if(have_to_rename(c))
        return true;
  }
  else if(dest.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(dest);
    if(have_to_rename(code_type.return_type()))
      return true;

    for(const auto &p : code_type.parameters())
    {
      if(have_to_rename(p.type()))
        return true;

      if(expr_map.find(p.get_identifier()) != expr_map.end())
        return true;
    }
  }
  else if(dest.id() == ID_symbol_type)
  {
    const irep_idt &identifier = to_symbol_type(dest).get_identifier();
    return type_map.find(identifier) != type_map.end();
  }
  else if(dest.id()==ID_c_enum_tag ||
          dest.id()==ID_struct_tag ||
          dest.id()==ID_union_tag)
    return type_map.find(to_tag_type(dest).get_identifier())!=type_map.end();
  else if(dest.id()==ID_array)
    return have_to_rename(to_array_type(dest).size());

  return false;
}
