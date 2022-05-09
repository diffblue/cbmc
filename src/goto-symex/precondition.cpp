/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "precondition.h"

#include <util/find_symbols.h>
#include <util/pointer_expr.h>

#include <pointer-analysis/goto_program_dereference.h>

#include "renaming_level.h"
#include "symex_target_equation.h"

class preconditiont
{
public:
  preconditiont(
    const namespacet &_ns,
    value_setst &_value_sets,
    const goto_programt::const_targett _target,
    const SSA_stept &_SSA_step,
    const goto_symex_statet &_s)
    : ns(_ns),
      value_sets(_value_sets),
      target(_target),
      SSA_step(_SSA_step),
      s(_s)
  {
  }

protected:
  const namespacet &ns;
  value_setst &value_sets;
  const goto_programt::const_targett target;
  const SSA_stept &SSA_step;
  const goto_symex_statet &s;
  void compute_rec(exprt &dest);

public:
  void compute(exprt &dest);

protected:
  void compute_address_of(exprt &dest);
};

void precondition(
  const namespacet &ns,
  value_setst &value_sets,
  const goto_programt::const_targett target,
  const symex_target_equationt &equation,
  const goto_symex_statet &s,
  exprt &dest)
{
  for(symex_target_equationt::SSA_stepst::const_reverse_iterator
      it=equation.SSA_steps.rbegin();
      it!=equation.SSA_steps.rend();
      it++)
  {
    preconditiont precondition(ns, value_sets, target, *it, s);
    precondition.compute(dest);
    if(dest.is_false())
      return;
  }
}

void preconditiont::compute_address_of(exprt &dest)
{
  if(dest.id()==ID_symbol)
  {
    // leave alone
  }
  else if(dest.id()==ID_index)
  {
    auto &index_expr = to_index_expr(dest);
    compute_address_of(index_expr.array());
    compute(index_expr.index());
  }
  else if(dest.id()==ID_member)
  {
    compute_address_of(to_member_expr(dest).compound());
  }
  else if(dest.id()==ID_dereference)
  {
    compute(to_dereference_expr(dest).pointer());
  }
}

void preconditiont::compute(exprt &dest)
{
  compute_rec(dest);
}

void preconditiont::compute_rec(exprt &dest)
{
  if(dest.id()==ID_address_of)
  {
    // only do index!
    compute_address_of(to_address_of_expr(dest).object());
  }
  else if(dest.id()==ID_dereference)
  {
    auto &deref_expr = to_dereference_expr(dest);

    const irep_idt &lhs_identifier=SSA_step.ssa_lhs.get_object_name();

    // aliasing may happen here

    bool may_alias = false;
    for(const exprt &e : value_sets.get_values(
          SSA_step.source.function_id, target, deref_expr.pointer()))
    {
      if(has_symbol(e, lhs_identifier, kindt::F_EXPR_BOTH))
      {
        may_alias = true;
        break;
      }
    }

    if(may_alias)
    {
      exprt tmp;
      tmp.swap(deref_expr.pointer());
      dereference(SSA_step.source.function_id, target, tmp, ns, value_sets);
      deref_expr.swap(tmp);
      compute_rec(deref_expr);
    }
    else
    {
      // nah, ok
      compute_rec(deref_expr.pointer());
    }
  }
  else if(dest==SSA_step.ssa_lhs.get_original_expr())
  {
    dest = get_original_name(SSA_step.ssa_rhs);
  }
  else
    Forall_operands(it, dest)
      compute_rec(*it);
}
