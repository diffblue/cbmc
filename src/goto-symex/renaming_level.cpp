/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Renaming levels

#include "renaming_level.h"

#include <util/namespace.h>
#include <util/ssa_expr.h>
#include <util/symbol.h>

#include "goto_symex_state.h"

renamedt<ssa_exprt, L0> symex_level0t::
operator()(ssa_exprt ssa_expr, const namespacet &ns, unsigned thread_nr) const
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

renamedt<ssa_exprt, L1> symex_level1t::
operator()(renamedt<ssa_exprt, L0> l0_expr) const
{
  if(!l0_expr.get().get_level_1().empty())
    return renamedt<ssa_exprt, L1>{std::move(l0_expr.value)};

  const irep_idt l0_name = l0_expr.get().get_l1_object_identifier();

  const auto it = current_names.find(l0_name);
  if(it == current_names.end())
    return renamedt<ssa_exprt, L1>{std::move(l0_expr.value)};

  // rename!
  l0_expr.value.set_level_1(it->second.second);
  return renamedt<ssa_exprt, L1>{std::move(l0_expr.value)};
}

ssa_exprt symex_level2t::operator()(ssa_exprt ssa_expr) const
{
  ssa_expr.set_level_2(current_count(ssa_expr.get_identifier()));
  return ssa_expr;
}

void symex_level1t::restore_from(
  const symex_renaming_levelt::current_namest &other)
{
  auto it = current_names.begin();
  for(const auto &pair : other)
  {
    while(it != current_names.end() && it->first < pair.first)
      ++it;
    if(it == current_names.end() || pair.first < it->first)
      current_names.insert(it, pair);
    else if(it != current_names.end())
    {
      PRECONDITION(it->first == pair.first);
      it->second = pair.second;
      ++it;
    }
  }
}

void get_original_name(exprt &expr)
{
  get_original_name(expr.type());

  if(expr.id() == ID_symbol && expr.get_bool(ID_C_SSA_symbol))
    expr = to_ssa_expr(expr).get_original_expr();
  else
    Forall_operands(it, expr)
      get_original_name(*it);
}

void get_original_name(typet &type)
{
  // rename all the symbols with their last known value

  if(type.id() == ID_array)
  {
    auto &array_type = to_array_type(type);
    get_original_name(array_type.subtype());
    get_original_name(array_type.size());
  }
  else if(type.id() == ID_struct || type.id() == ID_union)
  {
    struct_union_typet &s_u_type = to_struct_union_type(type);
    struct_union_typet::componentst &components = s_u_type.components();

    for(auto &component : components)
      get_original_name(component.type());
  }
  else if(type.id() == ID_pointer)
  {
    get_original_name(to_pointer_type(type).subtype());
  }
}
