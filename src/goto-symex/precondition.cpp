/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "precondition.h"
#include "goto_symex_state.h"

#include <util/find_symbols.h>

#include <pointer-analysis/goto_program_dereference.h>

#include <goto-programs/goto_model.h>

class preconditiont
{
public:
  preconditiont(
    const namespacet &_ns,
    value_setst &_value_sets,
    const goto_programt::const_targett _target,
    const symex_target_equationt::SSA_stept &_SSA_step,
    const goto_symex_statet &_s):
    ns(_ns),
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
  const symex_target_equationt::SSA_stept &SSA_step;
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
    DATA_INVARIANT(
      dest.operands().size() == 2, "index_exprt takes two operands.");
    compute_address_of(dest.op0());
    compute(dest.op1());
  }
  else if(dest.id()==ID_member)
  {
    DATA_INVARIANT(
      dest.operands().size() == 1, "member_exprt takes one operand.");
    compute_address_of(dest.op0());
  }
  else if(dest.id()==ID_dereference)
  {
    DATA_INVARIANT(
      dest.operands().size() == 1, "dereference_exprt takes one operand.");
    compute(dest.op0());
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
    DATA_INVARIANT(
      dest.operands().size() == 1, "address_of_exprt takes one operand.");
    compute_address_of(dest.op0());
  }
  else if(dest.id()==ID_dereference)
  {
    DATA_INVARIANT(
      dest.operands().size() == 1, "dereference_exprt takes one operand.");

    const irep_idt &lhs_identifier=SSA_step.ssa_lhs.get_object_name();

    // aliasing may happen here

    value_setst::valuest expr_set;
    value_sets.get_values(target, dest.op0(), expr_set);
    std::unordered_set<irep_idt> symbols;

    for(value_setst::valuest::const_iterator
        it=expr_set.begin();
        it!=expr_set.end();
        it++)
      find_symbols(*it, symbols);

    if(symbols.find(lhs_identifier)!=symbols.end())
    {
      // may alias!
      exprt tmp;
      tmp.swap(dest.op0());
      dereference(target, tmp, ns, value_sets);
      dest.swap(tmp);
      compute_rec(dest);
    }
    else
    {
      // nah, ok
      compute_rec(dest.op0());
    }
  }
  else if(dest==SSA_step.ssa_lhs.get_original_expr())
  {
    dest=SSA_step.ssa_rhs;
    s.get_original_name(dest);
  }
  else
    Forall_operands(it, dest)
      compute_rec(*it);
}
