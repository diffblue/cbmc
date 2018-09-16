/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "find_symbols.h"

#include "std_types.h"
#include "std_expr.h"

enum class kindt { F_TYPE, F_TYPE_NON_PTR, F_EXPR, F_BOTH };

void find_symbols(
  const exprt &src,
  find_symbols_sett &dest)
{
  find_symbols(src, dest, true, true);
}

void find_symbols(
  const exprt &src,
  find_symbols_sett &dest,
  bool current,
  bool next)
{
  if(src.id() == ID_symbol && current)
    dest.insert(to_symbol_expr(src).get_identifier());
  else if(src.id() == ID_next_symbol && next)
    dest.insert(src.get(ID_identifier));
  else
  {
    forall_operands(it, src)
      find_symbols(*it, dest, current, next);
  }
}

bool has_symbol(
  const exprt &src,
  const find_symbols_sett &symbols,
  bool current,
  bool next)
{
  if(src.id() == ID_symbol && current)
    return symbols.count(to_symbol_expr(src).get_identifier()) != 0;
  else if(src.id() == ID_next_symbol && next)
    return symbols.count(src.get(ID_identifier))!=0;
  else
  {
    forall_operands(it, src)
      if(has_symbol(*it, symbols, current, next))
        return true;
  }

  return false;
}

bool has_symbol(
  const exprt &src,
  const find_symbols_sett &symbols)
{
  return has_symbol(src, symbols, true, true);
}

void find_symbols(
  const exprt &src,
  std::set<exprt> &dest)
{
  if(src.id()==ID_symbol || src.id()==ID_next_symbol)
    dest.insert(src);
  else
  {
    forall_operands(it, src)
      find_symbols(*it, dest);
  }
}

void find_symbols(
  const exprt &src,
  std::set<symbol_exprt> &dest)
{
  if(src.id()==ID_symbol)
    dest.insert(to_symbol_expr(src));
  else
  {
    forall_operands(it, src)
      find_symbols(*it, dest);
  }
}

void find_symbols(kindt kind, const typet &src, find_symbols_sett &dest);

void find_symbols(kindt kind, const exprt &src, find_symbols_sett &dest)
{
  forall_operands(it, src)
    find_symbols(kind, *it, dest);

  find_symbols(kind, src.type(), dest);

  if(kind==kindt::F_BOTH || kind==kindt::F_EXPR)
  {
    if(src.id() == ID_symbol)
      dest.insert(to_symbol_expr(src).get_identifier());
    else if(src.id() == ID_next_symbol)
      dest.insert(src.get(ID_identifier));
  }

  const irept &c_sizeof_type=src.find(ID_C_c_sizeof_type);

  if(c_sizeof_type.is_not_nil())
    find_symbols(kind, static_cast<const typet &>(c_sizeof_type), dest);

  const irept &va_arg_type=src.find(ID_C_va_arg_type);

  if(va_arg_type.is_not_nil())
    find_symbols(kind, static_cast<const typet &>(va_arg_type), dest);
}

void find_symbols(kindt kind, const typet &src, find_symbols_sett &dest)
{
  if(kind!=kindt::F_TYPE_NON_PTR ||
     src.id()!=ID_pointer)
  {
    if(src.has_subtype())
      find_symbols(kind, src.subtype(), dest);

    forall_subtypes(it, src)
      find_symbols(kind, *it, dest);

    const irep_idt &typedef_name=src.get(ID_C_typedef);
    if(!typedef_name.empty())
      dest.insert(typedef_name);
  }

  if(src.id()==ID_struct ||
     src.id()==ID_union)
  {
    const struct_union_typet &struct_union_type=to_struct_union_type(src);

    for(const auto &c : struct_union_type.components())
      find_symbols(kind, c, dest);
  }
  else if(src.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(src);
    find_symbols(kind, code_type.return_type(), dest);

    for(const auto &p : code_type.parameters())
    {
      find_symbols(kind, p, dest);

      // irep_idt identifier=it->get_identifier();
      // if(!identifier.empty() && (kind==F_TYPE || kind==F_BOTH))
      //  dest.insert(identifier);
    }
  }
  else if(src.id() == ID_symbol_type)
    dest.insert(to_symbol_type(src).get_identifier());
  else if(src.id()==ID_array)
  {
    // do the size -- the subtype is already done
    find_symbols(kind, to_array_type(src).size(), dest);
  }
  else if(src.id()==ID_c_enum_tag)
  {
    dest.insert(to_c_enum_tag_type(src).get_identifier());
  }
  else if(src.id()==ID_struct_tag)
  {
    dest.insert(to_struct_tag_type(src).get_identifier());
  }
  else if(src.id()==ID_union_tag)
  {
    dest.insert(to_union_tag_type(src).get_identifier());
  }
}

void find_type_symbols(const exprt &src, find_symbols_sett &dest)
{
  find_symbols(kindt::F_TYPE, src, dest);
}

void find_type_symbols(const typet &src, find_symbols_sett &dest)
{
  find_symbols(kindt::F_TYPE, src, dest);
}

void find_non_pointer_type_symbols(
  const exprt &src,
  find_symbols_sett &dest)
{
  find_symbols(kindt::F_TYPE_NON_PTR, src, dest);
}

void find_non_pointer_type_symbols(
  const typet &src,
  find_symbols_sett &dest)
{
  find_symbols(kindt::F_TYPE_NON_PTR, src, dest);
}

void find_type_and_expr_symbols(const exprt &src, find_symbols_sett &dest)
{
  find_symbols(kindt::F_BOTH, src, dest);
}

void find_type_and_expr_symbols(const typet &src, find_symbols_sett &dest)
{
  find_symbols(kindt::F_BOTH, src, dest);
}
