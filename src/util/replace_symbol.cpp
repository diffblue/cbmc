/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "replace_symbol.h"

#include "expr_util.h"
#include "invariant.h"
#include "pointer_expr.h"
#include "std_expr.h"

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
  PRECONDITION_WITH_DIAGNOSTICS(
    old_expr.type() == new_expr.type(),
    "types to be replaced should match. old type:\n" +
      old_expr.type().pretty() + "\nnew.type:\n" + new_expr.type().pretty());
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
    "types to be replaced should match. s.type:\n" + s.type().pretty() +
      "\nit->second.type:\n" + it->second.type().pretty());
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
  else if(dest.id() == ID_let)
  {
    auto &let_expr = to_let_expr(dest);

    // first replace the assigned value expressions
    for(auto &op : let_expr.values())
      if(replace(op))
        result = false;

    // now set up the binding
    auto old_bindings = bindings;
    for(auto &variable : let_expr.variables())
      bindings.insert(variable.get_identifier());

    // now replace in the 'where' expression
    if(!replace(let_expr.where()))
      result = false;

    bindings = std::move(old_bindings);
  }
  else if(
    dest.id() == ID_array_comprehension || dest.id() == ID_exists ||
    dest.id() == ID_forall || dest.id() == ID_lambda)
  {
    auto &binding_expr = to_binding_expr(dest);

    auto old_bindings = bindings;
    for(auto &binding : binding_expr.variables())
      bindings.insert(binding.get_identifier());

    if(!replace(binding_expr.where()))
      result = false;

    bindings = std::move(old_bindings);
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
    if(bindings.find(identifier) != bindings.end())
      return false;
    else
      return replaces_symbol(identifier);
  }

  for(const auto &op : dest.operands())
  {
    if(have_to_replace(op))
      return true;
  }

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
    if(!replace(to_type_with_subtype(dest).subtype()))
      result=false;

  for(typet &subtype : to_type_with_subtypes(dest).subtypes())
  {
    if(!replace(subtype))
      result=false;
  }

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

    const exprt &spec_assigns =
      static_cast<const exprt &>(dest.find(ID_C_spec_assigns));
    if(spec_assigns.is_not_nil() && have_to_replace(spec_assigns))
      result &= replace(static_cast<exprt &>(dest.add(ID_C_spec_assigns)));

    const exprt &spec_frees =
      static_cast<const exprt &>(dest.find(ID_C_spec_frees));
    if(spec_frees.is_not_nil() && have_to_replace(spec_frees))
      result &= replace(static_cast<exprt &>(dest.add(ID_C_spec_frees)));

    const exprt &spec_ensures =
      static_cast<const exprt &>(dest.find(ID_C_spec_ensures));
    if(spec_ensures.is_not_nil() && have_to_replace(spec_ensures))
      result &= replace(static_cast<exprt &>(dest.add(ID_C_spec_ensures)));

    const exprt &spec_requires =
      static_cast<const exprt &>(dest.find(ID_C_spec_requires));
    if(spec_requires.is_not_nil() && have_to_replace(spec_requires))
      result &= replace(static_cast<exprt &>(dest.add(ID_C_spec_requires)));
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
    if(have_to_replace(to_type_with_subtype(dest).subtype()))
      return true;

  for(const typet &subtype : to_type_with_subtypes(dest).subtypes())
  {
    if(have_to_replace(subtype))
      return true;
  }

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

    const exprt &spec_assigns =
      static_cast<const exprt &>(dest.find(ID_C_spec_assigns));
    if(spec_assigns.is_not_nil() && have_to_replace(spec_assigns))
      return true;

    const exprt &spec_ensures =
      static_cast<const exprt &>(dest.find(ID_C_spec_ensures));
    if(spec_ensures.is_not_nil() && have_to_replace(spec_ensures))
      return true;

    const exprt &spec_requires =
      static_cast<const exprt &>(dest.find(ID_C_spec_requires));
    if(spec_requires.is_not_nil() && have_to_replace(spec_requires))
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

  if(require_lvalue && !is_assignable(s_copy))
    return true;

  // Note s_copy is no longer a symbol_exprt due to the replace operation,
  // and after this line `s` won't be either
  s = s_copy;

  return false;
}
