/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "postcondition.h"

#include <util/find_symbols.h>
#include <util/std_expr.h>

#include "goto_symex_state.h"

class postconditiont
{
public:
  postconditiont(
    const namespacet &_ns,
    const value_sett &_value_set,
    const symex_target_equationt::SSA_stept &_SSA_step,
    const goto_symex_statet &_s):
    ns(_ns),
    value_set(_value_set),
    SSA_step(_SSA_step),
    s(_s)
  {
  }

protected:
  const namespacet &ns;
  const value_sett &value_set;
  const symex_target_equationt::SSA_stept &SSA_step;
  const goto_symex_statet &s;

public:
  void compute(exprt &dest);

protected:
  void strengthen(exprt &dest);
  void weaken(exprt &dest);
  bool is_used_address_of(const exprt &expr, const irep_idt &identifier);
  bool is_used(const exprt &expr, const irep_idt &identifier);
};

void postcondition(
  const namespacet &ns,
  const value_sett &value_set,
  const symex_target_equationt &equation,
  const goto_symex_statet &s,
  exprt &dest)
{
  for(symex_target_equationt::SSA_stepst::const_iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end();
      it++)
  {
    postconditiont postcondition(ns, value_set, *it, s);
    postcondition.compute(dest);
    if(dest.is_false())
      return;
  }
}

bool postconditiont::is_used_address_of(
  const exprt &expr,
  const irep_idt &identifier)
{
  if(expr.id()==ID_symbol)
  {
    // leave alone
  }
  else if(expr.id()==ID_index)
  {
    DATA_INVARIANT(
      expr.operands().size() == 2, "index_exprt takes two operands.");

    return
      is_used_address_of(expr.op0(), identifier) ||
      is_used(expr.op1(), identifier);
  }
  else if(expr.id()==ID_member)
  {
    DATA_INVARIANT(
      expr.operands().size() == 1, "member_exprt takes one operand.");
    return is_used_address_of(expr.op0(), identifier);
  }
  else if(expr.id()==ID_dereference)
  {
    DATA_INVARIANT(
      expr.operands().size() == 1, "dereference_exprt takes one operand.");
    return is_used(expr.op0(), identifier);
  }

  return false;
}

void postconditiont::compute(exprt &dest)
{
  // weaken due to assignment
  weaken(dest);

  // strengthen due to assignment
  strengthen(dest);
}

void postconditiont::weaken(exprt &dest)
{
  if(dest.id()==ID_and &&
     dest.type()==bool_typet()) // this distributes over "and"
  {
    Forall_operands(it, dest)
      weaken(*it);

    return;
  }

  // we are lazy:
  // if lhs is mentioned in dest, we use "true".

  const irep_idt &lhs_identifier=SSA_step.ssa_lhs.get_object_name();

  if(is_used(dest, lhs_identifier))
    dest=true_exprt();

  // otherwise, no weakening needed
}

void postconditiont::strengthen(exprt &dest)
{
  const irep_idt &lhs_identifier=SSA_step.ssa_lhs.get_object_name();

  if(!is_used(SSA_step.ssa_rhs, lhs_identifier))
  {
    // we don't do arrays or structs
    if(SSA_step.ssa_lhs.type().id()==ID_array ||
       SSA_step.ssa_lhs.type().id()==ID_struct)
      return;

    equal_exprt equality(SSA_step.ssa_lhs, SSA_step.ssa_rhs);
    s.get_original_name(equality);

    if(dest.is_true())
      dest.swap(equality);
    else
      dest=and_exprt(dest, equality);
  }
}

bool postconditiont::is_used(
  const exprt &expr,
  const irep_idt &identifier)
{
  if(expr.id()==ID_address_of)
  {
    // only do index!
    DATA_INVARIANT(
      expr.operands().size() == 1, "address_of_exprt takes one operand.");
    return is_used_address_of(expr.op0(), identifier);
  }
  else if(expr.id()==ID_symbol &&
          expr.get_bool(ID_C_SSA_symbol))
  {
    return to_ssa_expr(expr).get_object_name()==identifier;
  }
  else if(expr.id()==ID_symbol)
  {
    return to_symbol_expr(expr).get_identifier() == identifier;
  }
  else if(expr.id()==ID_dereference)
  {
    DATA_INVARIANT(
      expr.operands().size() == 1, "dereference_exprt takes one operand.");

    // aliasing may happen here

    value_setst::valuest expr_set;
    value_set.get_value_set(expr.op0(), expr_set, ns);
    std::unordered_set<irep_idt> symbols;

    for(value_setst::valuest::const_iterator
        it=expr_set.begin();
        it!=expr_set.end();
        it++)
    {
      exprt tmp(*it);
      s.get_original_name(tmp);
      find_symbols(tmp, symbols);
    }

    return symbols.find(identifier)!=symbols.end();
  }
  else
    forall_operands(it, expr)
      if(is_used(*it, identifier))
        return true;

  return false;
}
