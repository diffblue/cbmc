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

void symex_level0t::
operator()(ssa_exprt &ssa_expr, const namespacet &ns, unsigned thread_nr)
{
  // already renamed?
  if(!ssa_expr.get_level_0().empty())
    return;

  const irep_idt &obj_identifier = ssa_expr.get_object_name();

  // guards are not L0-renamed
  if(obj_identifier == "goto_symex::\\guard")
    return;

  const symbolt *s;
  const bool found_l0 = !ns.lookup(obj_identifier, s);
  INVARIANT(found_l0, "level0: failed to find " + id2string(obj_identifier));

  // don't rename shared variables or functions
  if(s->type.id() == ID_code || s->is_shared())
    return;

  // rename!
  ssa_expr.set_level_0(thread_nr);
}

void symex_level1t::operator()(ssa_exprt &ssa_expr)
{
  // already renamed?
  if(!ssa_expr.get_level_1().empty())
    return;

  const irep_idt l0_name = ssa_expr.get_l1_object_identifier();

  const auto it = current_names.find(l0_name);
  if(it == current_names.end())
    return;

  // rename!
  ssa_expr.set_level_1(it->second.second);
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
