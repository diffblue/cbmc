/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "replace_symbol.h"

#include "expr_util.h"
#include "invariant.h"
#include "std_expr.h"
#include "std_types.h"

replace_symbolt::replace_symbolt()
{
}

replace_symbolt::~replace_symbolt()
{
}

void replace_symbolt::insert(
  const symbol_exprt &old_expr,
  const exprt &new_expr)
{
  PRECONDITION(old_expr.type() == new_expr.type());
  expr_map.insert(std::pair<irep_idt, exprt>(
    old_expr.get_identifier(), new_expr));
}

void replace_symbolt::set(const symbol_exprt &old_expr, const exprt &new_expr)
{
  PRECONDITION(old_expr.type() == new_expr.type());
  expr_map[old_expr.get_identifier()] = new_expr;
}


bool replace_symbolt::replace_symbol_expr(symbol_exprt &s) const
{
  expr_mapt::const_iterator it = expr_map.find(s.get_identifier());

  if(it == expr_map.end())
    return true;

  DATA_INVARIANT(
    s.type() == it->second.type(),
    "type of symbol to be replaced should match");
  static_cast<exprt &>(s) = it->second;

  return false;
}

bool replace_symbolt::replace(exprt &dest) const
{
  bool result=true; // unchanged

  // first look at type

  const exprt &const_dest(dest);
  if(have_to_replace(const_dest.type()))
    if(!replace(dest.type()))
      result=false;

  // now do expression itself

  if(!have_to_replace(dest))
    return result;

  if(dest.id()==ID_member)
  {
    member_exprt &me=to_member_expr(dest);

    if(!replace(me.struct_op()))
      result=false;
  }
  else if(dest.id()==ID_index)
  {
    index_exprt &ie=to_index_expr(dest);

    if(!replace(ie.array()))
      result=false;

    if(!replace(ie.index()))
      result=false;
  }
  else if(dest.id()==ID_address_of)
  {
    address_of_exprt &aoe=to_address_of_expr(dest);

    if(!replace(aoe.object()))
      result=false;
  }
  else if(dest.id()==ID_symbol)
  {
    if(!replace_symbol_expr(to_symbol_expr(dest)))
      return false;
  }
  else
  {
    Forall_operands(it, dest)
      if(!replace(*it))
        result=false;
  }

  const typet &c_sizeof_type =
    static_cast<const typet&>(dest.find(ID_C_c_sizeof_type));
  if(c_sizeof_type.is_not_nil() && have_to_replace(c_sizeof_type))
    result &= replace(static_cast<typet&>(dest.add(ID_C_c_sizeof_type)));

  const typet &va_arg_type =
    static_cast<const typet&>(dest.find(ID_C_va_arg_type));
  if(va_arg_type.is_not_nil() && have_to_replace(va_arg_type))
    result &= replace(static_cast<typet&>(dest.add(ID_C_va_arg_type)));

  return result;
}

bool replace_symbolt::have_to_replace(const exprt &dest) const
{
  if(empty())
    return false;

  // first look at type

  if(have_to_replace(dest.type()))
    return true;

  // now do expression itself

  if(dest.id()==ID_symbol)
  {
    const irep_idt &identifier = to_symbol_expr(dest).get_identifier();
    return replaces_symbol(identifier);
  }

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

    for(auto &c : struct_union_type.components())
      if(!replace(c))
        result=false;
  }
  else if(dest.id()==ID_code)
  {
    code_typet &code_type=to_code_type(dest);
    if(!replace(code_type.return_type()))
      result = false;

    for(auto &p : code_type.parameters())
      if(!replace(p))
        result=false;
  }
  else if(dest.id()==ID_array)
  {
    array_typet &array_type=to_array_type(dest);
    if(!replace(array_type.size()))
      result=false;
  }

  return result;
}

bool replace_symbolt::have_to_replace(const typet &dest) const
{
  if(expr_map.empty())
    return false;

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

    for(const auto &c : struct_union_type.components())
      if(have_to_replace(c))
        return true;
  }
  else if(dest.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(dest);
    if(have_to_replace(code_type.return_type()))
      return true;

    for(const auto &p : code_type.parameters())
      if(have_to_replace(p))
        return true;
  }
  else if(dest.id()==ID_array)
    return have_to_replace(to_array_type(dest).size());

  return false;
}

void unchecked_replace_symbolt::insert(
  const symbol_exprt &old_expr,
  const exprt &new_expr)
{
  expr_map.emplace(old_expr.get_identifier(), new_expr);
}

bool unchecked_replace_symbolt::replace_symbol_expr(symbol_exprt &s) const
{
  expr_mapt::const_iterator it = expr_map.find(s.get_identifier());

  if(it == expr_map.end())
    return true;

  static_cast<exprt &>(s) = it->second;

  return false;
}

bool address_of_aware_replace_symbolt::replace(exprt &dest) const
{
  const exprt &const_dest(dest);
  if(!require_lvalue && const_dest.id() != ID_address_of)
    return unchecked_replace_symbolt::replace(dest);

  bool result = true; // unchanged

  // first look at type
  if(have_to_replace(const_dest.type()))
  {
    const set_require_lvalue_and_backupt backup(require_lvalue, false);
    if(!unchecked_replace_symbolt::replace(dest.type()))
      result = false;
  }

  // now do expression itself

  if(!have_to_replace(dest))
    return result;

  if(dest.id() == ID_index)
  {
    index_exprt &ie = to_index_expr(dest);

    // Could yield non l-value.
    if(!replace(ie.array()))
      result = false;

    const set_require_lvalue_and_backupt backup(require_lvalue, false);
    if(!replace(ie.index()))
      result = false;
  }
  else if(dest.id() == ID_address_of)
  {
    address_of_exprt &aoe = to_address_of_expr(dest);

    const set_require_lvalue_and_backupt backup(require_lvalue, true);
    if(!replace(aoe.object()))
      result = false;
  }
  else
  {
    if(!unchecked_replace_symbolt::replace(dest))
      return false;
  }

  const set_require_lvalue_and_backupt backup(require_lvalue, false);

  const typet &c_sizeof_type =
    static_cast<const typet &>(dest.find(ID_C_c_sizeof_type));
  if(c_sizeof_type.is_not_nil() && have_to_replace(c_sizeof_type))
    result &= unchecked_replace_symbolt::replace(
      static_cast<typet &>(dest.add(ID_C_c_sizeof_type)));

  const typet &va_arg_type =
    static_cast<const typet &>(dest.find(ID_C_va_arg_type));
  if(va_arg_type.is_not_nil() && have_to_replace(va_arg_type))
    result &= unchecked_replace_symbolt::replace(
      static_cast<typet &>(dest.add(ID_C_va_arg_type)));

  return result;
}

bool address_of_aware_replace_symbolt::replace_symbol_expr(
  symbol_exprt &s) const
{
  symbol_exprt s_copy = s;
  if(unchecked_replace_symbolt::replace_symbol_expr(s_copy))
    return true;

  if(require_lvalue && !is_lvalue(s_copy))
    return true;

  // Note s_copy is no longer a symbol_exprt due to the replace operation,
  // and after this line `s` won't be either
  s = s_copy;

  return false;
}
