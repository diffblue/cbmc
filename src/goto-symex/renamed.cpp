/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Class for expressions or types renamed up to a given level

#include "renamed.h"
#include <util/ssa_expr.h>
#include <util/std_expr.h>

template <levelt level>
renamedt<exprt, level> make_renamed(constant_exprt constant)
{
  return renamedt<exprt, level>(std::move(constant));
}

// Force template instantiations for the three levels
template renamedt<exprt, L0> make_renamed(constant_exprt constant);
template renamedt<exprt, L1> make_renamed(constant_exprt constant);
template renamedt<exprt, L2> make_renamed(constant_exprt constant);

bool is_l1_renamed(const exprt &expr)
{
  if(expr.id() == ID_symbol)
  {
    const auto &type = expr.type();
    if(!expr.get_bool(ID_C_SSA_symbol))
      return type.id() == ID_code || type.id() == ID_mathematical_function;
    if(!to_ssa_expr(expr).get_level_2().empty())
      return false;
    if(to_ssa_expr(expr).get_original_expr().type() != type)
      return false;
  }
  else
  {
    forall_operands(it, expr)
      if(!is_l1_renamed(*it))
        return false;
  }

  return true;
}

bool is_l2_renamed(const typet &type)
{
  if(type.id() == ID_array)
  {
    if(!is_l2_renamed(to_array_type(type).size()))
      return false;
  }
  else if(type.id() == ID_struct || type.id() == ID_union)
  {
    for(const auto &c : to_struct_union_type(type).components())
      if(!is_l2_renamed(c.type()))
        return false;
  }
  else if(
    type.has_subtype() && !is_l2_renamed(to_type_with_subtype(type).subtype()))
  {
    return false;
  }
  return true;
}

bool is_l2_renamed(const exprt &expr)
{
  if(!is_l2_renamed(expr.type()))
    return false;

  if(
    expr.id() == ID_address_of &&
    to_address_of_expr(expr).object().id() == ID_symbol)
  {
    return is_l1_renamed(to_address_of_expr(expr).object());
  }
  else if(
    expr.id() == ID_address_of &&
    to_address_of_expr(expr).object().id() == ID_index)
  {
    const auto index_expr = to_index_expr(to_address_of_expr(expr).object());
    return is_l1_renamed(index_expr.array()) &&
           is_l2_renamed(index_expr.index());
  }
  else if(expr.id() == ID_symbol)
  {
    const auto &type = expr.type();
    if(!expr.get_bool(ID_C_SSA_symbol))
      return (type.id() == ID_code || type.id() == ID_mathematical_function);
    if(to_ssa_expr(expr).get_level_2().empty())
      return false;
    if(to_ssa_expr(expr).get_original_expr().type() != type)
      return false;
  }
  else
  {
    forall_operands(it, expr)
      if(!is_l2_renamed(*it))
        return false;
  }
  return true;
}

optionalt<renamedt<exprt, L1>> check_l1_renaming(exprt expr)
{
  if(is_l1_renamed(expr))
    return renamedt<exprt, L1>(std::move(expr));
  return {};
}

optionalt<renamedt<exprt, L2>> check_l2_renaming(exprt expr)
{
  if(is_l2_renamed(expr))
    return renamedt<exprt, L2>(std::move(expr));
  return {};
}

optionalt<renamedt<typet, L2>> check_l2_renaming(typet type)
{
  if(is_l2_renamed(type))
    return renamedt<typet, L2>(std::move(type));
  return {};
}
