/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "find_symbols.h"

#include "c_types.h"
#include "expr_iterator.h"
#include "range.h"
#include "std_expr.h"

bool has_symbol(const exprt &src, const find_symbols_sett &symbols)
{
  if(src.id() == ID_symbol)
    return symbols.count(to_symbol_expr(src).get_identifier()) != 0;
  else
  {
    forall_operands(it, src)
      if(has_symbol(*it, symbols))
        return true;
  }

  return false;
}

static bool find_symbols(
  symbol_kindt,
  const typet &,
  std::function<bool(const symbol_exprt &)>);

static bool find_symbols(
  symbol_kindt kind,
  const exprt &src,
  std::function<bool(const symbol_exprt &)> op)
{
  forall_operands(it, src)
  {
    if(!find_symbols(kind, *it, op))
      return false;
  }

  if(!find_symbols(kind, src.type(), op))
    return false;

  if(kind == symbol_kindt::F_ALL || kind == symbol_kindt::F_EXPR)
  {
    if(src.id() == ID_symbol && !op(to_symbol_expr(src)))
      return false;
  }

  const irept &c_sizeof_type=src.find(ID_C_c_sizeof_type);

  if(
    c_sizeof_type.is_not_nil() &&
    !find_symbols(kind, static_cast<const typet &>(c_sizeof_type), op))
  {
    return false;
  }

  const irept &va_arg_type=src.find(ID_C_va_arg_type);

  if(
    va_arg_type.is_not_nil() &&
    !find_symbols(kind, static_cast<const typet &>(va_arg_type), op))
  {
    return false;
  }

  return true;
}

static bool find_symbols(
  symbol_kindt kind,
  const typet &src,
  std::function<bool(const symbol_exprt &)> op)
{
  if(kind != symbol_kindt::F_TYPE_NON_PTR || src.id() != ID_pointer)
  {
    if(
      src.has_subtype() &&
      !find_symbols(kind, to_type_with_subtype(src).subtype(), op))
    {
      return false;
    }

    for(const typet &subtype : to_type_with_subtypes(src).subtypes())
    {
      if(!find_symbols(kind, subtype, op))
        return false;
    }

    if(
      kind == symbol_kindt::F_TYPE || kind == symbol_kindt::F_TYPE_NON_PTR ||
      kind == symbol_kindt::F_ALL)
    {
      const irep_idt &typedef_name = src.get(ID_C_typedef);
      if(!typedef_name.empty() && !op(symbol_exprt{typedef_name, typet{}}))
        return false;
    }
  }

  if(src.id()==ID_struct ||
     src.id()==ID_union)
  {
    const struct_union_typet &struct_union_type=to_struct_union_type(src);

    for(const auto &c : struct_union_type.components())
    {
      if(!find_symbols(kind, c, op))
        return false;
    }
  }
  else if(src.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(src);
    if(!find_symbols(kind, code_type.return_type(), op))
      return false;

    for(const auto &p : code_type.parameters())
    {
      if(!find_symbols(kind, p, op))
        return false;
    }
  }
  else if(src.id()==ID_array)
  {
    // do the size -- the subtype is already done
    if(!find_symbols(kind, to_array_type(src).size(), op))
      return false;
  }
  else if(
    kind == symbol_kindt::F_TYPE || kind == symbol_kindt::F_TYPE_NON_PTR ||
    kind == symbol_kindt::F_ALL)
  {
    if(src.id() == ID_c_enum_tag)
    {
      if(!op(symbol_exprt{to_c_enum_tag_type(src).get_identifier(), typet{}}))
        return false;
    }
    else if(src.id() == ID_struct_tag)
    {
      if(!op(symbol_exprt{to_struct_tag_type(src).get_identifier(), typet{}}))
        return false;
    }
    else if(src.id() == ID_union_tag)
    {
      if(!op(symbol_exprt{to_union_tag_type(src).get_identifier(), typet{}}))
        return false;
    }
  }

  return true;
}

void find_symbols(const exprt &src, std::set<symbol_exprt> &dest)
{
  find_symbols(symbol_kindt::F_EXPR, src, [&dest](const symbol_exprt &e) {
    dest.insert(e);
    return true;
  });
}

bool has_symbol(const exprt &src, const irep_idt &identifier, symbol_kindt kind)
{
  return !find_symbols(kind, src, [&identifier](const symbol_exprt &e) {
    return e.get_identifier() != identifier;
  });
}

void find_type_symbols(const exprt &src, find_symbols_sett &dest)
{
  find_symbols(symbol_kindt::F_TYPE, src, [&dest](const symbol_exprt &e) {
    dest.insert(e.get_identifier());
    return true;
  });
}

void find_type_symbols(const typet &src, find_symbols_sett &dest)
{
  find_symbols(symbol_kindt::F_TYPE, src, [&dest](const symbol_exprt &e) {
    dest.insert(e.get_identifier());
    return true;
  });
}

void find_non_pointer_type_symbols(
  const exprt &src,
  find_symbols_sett &dest)
{
  find_symbols(
    symbol_kindt::F_TYPE_NON_PTR, src, [&dest](const symbol_exprt &e) {
      dest.insert(e.get_identifier());
      return true;
    });
}

void find_non_pointer_type_symbols(
  const typet &src,
  find_symbols_sett &dest)
{
  find_symbols(
    symbol_kindt::F_TYPE_NON_PTR, src, [&dest](const symbol_exprt &e) {
      dest.insert(e.get_identifier());
      return true;
    });
}

void find_type_and_expr_symbols(const exprt &src, find_symbols_sett &dest)
{
  find_symbols(symbol_kindt::F_ALL, src, [&dest](const symbol_exprt &e) {
    dest.insert(e.get_identifier());
    return true;
  });
}

void find_type_and_expr_symbols(const typet &src, find_symbols_sett &dest)
{
  find_symbols(symbol_kindt::F_ALL, src, [&dest](const symbol_exprt &e) {
    dest.insert(e.get_identifier());
    return true;
  });
}

void find_symbols_or_nexts(const exprt &src, find_symbols_sett &dest)
{
  find_symbols(symbol_kindt::F_EXPR, src, [&dest](const symbol_exprt &e) {
    dest.insert(e.get_identifier());
    return true;
  });
}

void find_symbols(const exprt &src, find_symbols_sett &dest)
{
  find_symbols(symbol_kindt::F_EXPR, src, [&dest](const symbol_exprt &e) {
    dest.insert(e.get_identifier());
    return true;
  });
}
