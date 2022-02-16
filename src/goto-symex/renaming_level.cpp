/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Renaming levels

#include "renaming_level.h"

#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/ssa_expr.h>
#include <util/symbol.h>

#include "goto_symex_state.h"

renamedt<ssa_exprt, L0>
symex_level0(ssa_exprt ssa_expr, const namespacet &ns, std::size_t thread_nr)
{
  // already renamed?
  if(!ssa_expr.get_level_0().empty())
    return renamedt<ssa_exprt, L0>{std::move(ssa_expr)};

  const irep_idt &obj_identifier = ssa_expr.get_object_name();

  // guards are not L0-renamed
  if(obj_identifier == goto_symex_statet::guard_identifier())
    return renamedt<ssa_exprt, L0>{std::move(ssa_expr)};

  const symbolt *s;
  const bool found_l0 = !ns.lookup(obj_identifier, s);
  INVARIANT(found_l0, "level0: failed to find " + id2string(obj_identifier));

  // don't rename shared variables or functions
  if(s->type.id() == ID_code || s->is_shared())
    return renamedt<ssa_exprt, L0>{std::move(ssa_expr)};

  // rename!
  ssa_expr.set_level_0(thread_nr);
  return renamedt<ssa_exprt, L0>{ssa_expr};
}

void symex_level1t::insert(
  const renamedt<ssa_exprt, L0> &ssa,
  std::size_t index)
{
  current_names.insert(
    ssa.get().get_identifier(), std::make_pair(ssa.get(), index));
}

optionalt<std::pair<ssa_exprt, std::size_t>> symex_level1t::insert_or_replace(
  const renamedt<ssa_exprt, L0> &ssa,
  std::size_t index)
{
  const irep_idt &identifier = ssa.get().get_identifier();
  const auto old_value = current_names.find(identifier);
  if(old_value)
  {
    std::pair<ssa_exprt, std::size_t> result = *old_value;
    current_names.replace(identifier, std::make_pair(ssa.get(), index));
    return result;
  }
  current_names.insert(identifier, std::make_pair(ssa.get(), index));
  return {};
}

bool symex_level1t::has(const renamedt<ssa_exprt, L0> &ssa) const
{
  return current_names.has_key(ssa.get().get_identifier());
}

renamedt<ssa_exprt, L1> symex_level1t::
operator()(renamedt<ssa_exprt, L0> l0_expr) const
{
  if(
    !l0_expr.get().get_level_1().empty() ||
    !l0_expr.get().get_level_2().empty())
  {
    return renamedt<ssa_exprt, L1>{std::move(l0_expr.value())};
  }

  const irep_idt l0_name = l0_expr.get().get_l1_object_identifier();

  const auto r_opt = current_names.find(l0_name);

  if(!r_opt)
  {
    return renamedt<ssa_exprt, L1>{std::move(l0_expr.value())};
  }

  // rename!
  l0_expr.value().set_level_1(r_opt->get().second);
  return renamedt<ssa_exprt, L1>{std::move(l0_expr.value())};
}

renamedt<ssa_exprt, L2> symex_level2t::
operator()(renamedt<ssa_exprt, L1> l1_expr) const
{
  if(!l1_expr.get().get_level_2().empty())
    return renamedt<ssa_exprt, L2>{std::move(l1_expr.value())};
  l1_expr.value().set_level_2(latest_index(l1_expr.get().get_identifier()));
  return renamedt<ssa_exprt, L2>{std::move(l1_expr.value())};
}

void symex_level1t::restore_from(const symex_level1t &other)
{
  symex_renaming_levelt::delta_viewt delta_view;
  other.current_names.get_delta_view(current_names, delta_view, false);

  for(const auto &delta_item : delta_view)
  {
    if(!delta_item.is_in_both_maps())
    {
      current_names.insert(delta_item.k, delta_item.m);
    }
    else
    {
      if(delta_item.m != delta_item.get_other_map_value())
      {
        current_names.replace(delta_item.k, delta_item.m);
      }
    }
  }
}

unsigned symex_level2t::latest_index(const irep_idt &identifier) const
{
  const auto r_opt = current_names.find(identifier);
  return !r_opt ? 0 : r_opt->get().second;
}

std::size_t symex_level2t::increase_generation(
  const irep_idt &l1_identifier,
  const ssa_exprt &lhs,
  std::function<std::size_t(const irep_idt &)> fresh_l2_name_provider)
{
  const std::size_t n = fresh_l2_name_provider(l1_identifier);

  if(const auto r_opt = current_names.find(l1_identifier))
  {
    std::pair<ssa_exprt, std::size_t> copy = r_opt->get();
    copy.second = n;
    current_names.replace(l1_identifier, std::move(copy));
  }
  else
  {
    current_names.insert(l1_identifier, std::make_pair(lhs, n));
  }

  return n;
}

exprt get_original_name(exprt expr)
{
  expr.type() = get_original_name(std::move(expr.type()));

  if(is_ssa_expr(expr))
    return to_ssa_expr(expr).get_original_expr();
  else
  {
    Forall_operands(it, expr)
      *it = get_original_name(std::move(*it));
    return expr;
  }
}

typet get_original_name(typet type)
{
  // rename all the symbols with their last known value

  if(type.id() == ID_array)
  {
    auto &array_type = to_array_type(type);
    array_type.element_type() =
      get_original_name(std::move(array_type.element_type()));
    array_type.size() = get_original_name(std::move(array_type.size()));
  }
  else if(type.id() == ID_struct || type.id() == ID_union)
  {
    struct_union_typet &s_u_type = to_struct_union_type(type);
    struct_union_typet::componentst &components = s_u_type.components();

    for(auto &component : components)
      component.type() = get_original_name(std::move(component.type()));
  }
  else if(type.id() == ID_pointer)
  {
    to_pointer_type(type).base_type() =
      get_original_name(std::move(to_pointer_type(type).base_type()));
  }
  return type;
}

bool check_renaming(const typet &type)
{
  if(type.id() == ID_array)
    return check_renaming(to_array_type(type).size());
  else if(type.id() == ID_struct || type.id() == ID_union)
  {
    for(const auto &c : to_struct_union_type(type).components())
      if(check_renaming(c.type()))
        return true;
  }
  else if(type.has_subtype())
    return check_renaming(to_type_with_subtype(type).subtype());

  return false;
}

bool check_renaming_l1(const exprt &expr)
{
  if(check_renaming(expr.type()))
    return true;

  if(expr.id() == ID_symbol)
  {
    const auto &type = expr.type();
    if(!expr.get_bool(ID_C_SSA_symbol))
      return type.id() != ID_code && type.id() != ID_mathematical_function;
    if(!to_ssa_expr(expr).get_level_2().empty())
      return true;
    if(to_ssa_expr(expr).get_original_expr().type() != type)
      return true;
  }
  else
  {
    forall_operands(it, expr)
      if(check_renaming_l1(*it))
        return true;
  }

  return false;
}

bool check_renaming(const exprt &expr)
{
  if(check_renaming(expr.type()))
    return true;

  if(
    expr.id() == ID_address_of &&
    to_address_of_expr(expr).object().id() == ID_symbol)
  {
    return check_renaming_l1(to_address_of_expr(expr).object());
  }
  else if(
    expr.id() == ID_address_of &&
    to_address_of_expr(expr).object().id() == ID_index)
  {
    const auto index_expr = to_index_expr(to_address_of_expr(expr).object());
    return check_renaming_l1(index_expr.array()) ||
           check_renaming(index_expr.index());
  }
  else if(expr.id() == ID_symbol)
  {
    const auto &type = expr.type();
    if(!expr.get_bool(ID_C_SSA_symbol))
      return type.id() != ID_code && type.id() != ID_mathematical_function;
    if(to_ssa_expr(expr).get_level_2().empty())
      return true;
    if(to_ssa_expr(expr).get_original_expr().type() != type)
      return true;
  }
  else if(expr.id() == ID_nil)
  {
    return expr != nil_exprt{};
  }
  else
  {
    forall_operands(it, expr)
      if(check_renaming(*it))
        return true;
  }

  return false;
}
