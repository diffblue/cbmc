/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "find_symbols.h"

#include "c_types.h"
#include "std_expr.h"

/// Kinds of symbols to be considered by \ref find_symbols.
enum class symbol_kindt
{
  /// Struct, union, or enum tag symbols.
  F_TYPE,
  /// Struct, union, or enum tag symbols when the expression using them is not a
  /// pointer.
  F_TYPE_NON_PTR,
  /// Symbol expressions.
  F_EXPR,
  /// Symbol expressions, but excluding bound variables.
  F_EXPR_FREE,
  /// All of the above.
  F_ALL
};

/// Find identifiers with id ID_symbol of the sub expressions and the subs with
/// ID in \p subs_to_find
/// considering both free and bound variables, as well as any type tags.
static bool find_symbols(
  symbol_kindt,
  const typet &,
  std::function<bool(const symbol_exprt &)>,
  std::unordered_set<irep_idt> &bindings,
  const std::vector<irep_idt> &subs_to_find);

static bool find_symbols(
  symbol_kindt kind,
  const exprt &src,
  std::function<bool(const symbol_exprt &)> op,
  std::unordered_set<irep_idt> &bindings,
  const std::vector<irep_idt> &subs_to_find)
{
  if(kind == symbol_kindt::F_EXPR_FREE)
  {
    if(src.id() == ID_forall || src.id() == ID_exists || src.id() == ID_lambda)
    {
      const auto &binding_expr = to_binding_expr(src);
      std::unordered_set<irep_idt> new_bindings{bindings};
      for(const auto &v : binding_expr.variables())
        new_bindings.insert(v.get_identifier());

      if(!find_symbols(
           kind, binding_expr.where(), op, new_bindings, subs_to_find))
        return false;

      return find_symbols(
        kind, binding_expr.type(), op, bindings, subs_to_find);
    }
    else if(src.id() == ID_let)
    {
      const auto &let_expr = to_let_expr(src);
      std::unordered_set<irep_idt> new_bindings{bindings};
      for(const auto &v : let_expr.variables())
        new_bindings.insert(v.get_identifier());

      if(!find_symbols(kind, let_expr.where(), op, new_bindings, subs_to_find))
        return false;

      if(!find_symbols(kind, let_expr.op1(), op, new_bindings, subs_to_find))
        return false;

      return find_symbols(kind, let_expr.type(), op, bindings, subs_to_find);
    }
  }

  for(const auto &src_op : src.operands())
  {
    if(!find_symbols(kind, src_op, op, bindings, subs_to_find))
      return false;
  }

  // Go over all named subs with id in subs_to_find
  // and find symbols recursively.
  for(const auto &sub_to_find : subs_to_find)
  {
    auto sub_expr = static_cast<const exprt &>(src.find(sub_to_find));
    if(sub_expr.is_not_nil())
    {
      for(const auto &sub_op : sub_expr.operands())
      {
        if(!find_symbols(kind, sub_op, op, bindings, subs_to_find))
          return false;
      }
    }
  }

  if(!find_symbols(kind, src.type(), op, bindings, subs_to_find))
    return false;

  if(src.id() == ID_symbol)
  {
    const symbol_exprt &s = to_symbol_expr(src);

    if(kind == symbol_kindt::F_ALL || kind == symbol_kindt::F_EXPR)
    {
      if(!op(s))
        return false;
    }
    else if(kind == symbol_kindt::F_EXPR_FREE)
    {
      if(bindings.find(s.get_identifier()) == bindings.end() && !op(s))
        return false;
    }
  }

  const irept &c_sizeof_type = src.find(ID_C_c_sizeof_type);

  if(
    c_sizeof_type.is_not_nil() && !find_symbols(
                                    kind,
                                    static_cast<const typet &>(c_sizeof_type),
                                    op,
                                    bindings,
                                    subs_to_find))
  {
    return false;
  }

  const irept &va_arg_type=src.find(ID_C_va_arg_type);

  if(
    va_arg_type.is_not_nil() && !find_symbols(
                                  kind,
                                  static_cast<const typet &>(va_arg_type),
                                  op,
                                  bindings,
                                  subs_to_find))
  {
    return false;
  }

  return true;
}

/// Find identifiers with id ID_symbol of the sub expressions and the subs with
/// ID in \p subs_to_find
/// considering both free and bound variables, as well as any type tags.
static bool find_symbols(
  symbol_kindt kind,
  const typet &src,
  std::function<bool(const symbol_exprt &)> op,
  std::unordered_set<irep_idt> &bindings,
  const std::vector<irep_idt> &subs_to_find)
{
  if(kind != symbol_kindt::F_TYPE_NON_PTR || src.id() != ID_pointer)
  {
    if(
      src.has_subtype() &&
      !find_symbols(
        kind, to_type_with_subtype(src).subtype(), op, bindings, subs_to_find))
    {
      return false;
    }

    for(const typet &subtype : to_type_with_subtypes(src).subtypes())
    {
      if(!find_symbols(kind, subtype, op, bindings, subs_to_find))
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
      if(!find_symbols(kind, c, op, bindings, subs_to_find))
        return false;
    }
  }
  else if(src.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(src);
    if(!find_symbols(kind, code_type.return_type(), op, bindings, subs_to_find))
      return false;

    for(const auto &p : code_type.parameters())
    {
      if(!find_symbols(kind, p, op, bindings, subs_to_find))
        return false;
    }
  }
  else if(src.id()==ID_array)
  {
    // do the size -- the subtype is already done
    if(!find_symbols(
         kind, to_array_type(src).size(), op, bindings, subs_to_find))
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

static bool find_symbols(
  symbol_kindt kind,
  const typet &type,
  std::function<bool(const symbol_exprt &)> op,
  const std::vector<irep_idt> &subs_to_find = {})
{
  std::unordered_set<irep_idt> bindings;
  return find_symbols(kind, type, op, bindings, subs_to_find);
}

static bool find_symbols(
  symbol_kindt kind,
  const exprt &src,
  std::function<bool(const symbol_exprt &)> op,
  const std::vector<irep_idt> &subs_to_find = {})
{
  std::unordered_set<irep_idt> bindings;
  return find_symbols(kind, src, op, bindings, subs_to_find);
}

void find_symbols(const exprt &src, std::set<symbol_exprt> &dest)
{
  find_symbols(symbol_kindt::F_EXPR, src, [&dest](const symbol_exprt &e) {
    dest.insert(e);
    return true;
  });
}

bool has_symbol_expr(
  const exprt &src,
  const irep_idt &identifier,
  bool include_bound_symbols)
{
  return !find_symbols(
    include_bound_symbols ? symbol_kindt::F_EXPR : symbol_kindt::F_EXPR_FREE,
    src,
    [&identifier](const symbol_exprt &e) {
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

void find_type_and_expr_symbols(
  const exprt &src,
  find_symbols_sett &dest,
  const std::vector<irep_idt> &subs_to_find)
{
  find_symbols(
    symbol_kindt::F_ALL,
    src,
    [&dest](const symbol_exprt &e) {
      dest.insert(e.get_identifier());
      return true;
    },
    subs_to_find);
}

void find_type_and_expr_symbols(
  const typet &src,
  find_symbols_sett &dest,
  const std::vector<irep_idt> &subs_to_find)
{
  find_symbols(
    symbol_kindt::F_ALL,
    src,
    [&dest](const symbol_exprt &e) {
      dest.insert(e.get_identifier());
      return true;
    },
    subs_to_find);
}

void find_symbols(const exprt &src, find_symbols_sett &dest)
{
  find_symbols(symbol_kindt::F_EXPR, src, [&dest](const symbol_exprt &e) {
    dest.insert(e.get_identifier());
    return true;
  });
}
