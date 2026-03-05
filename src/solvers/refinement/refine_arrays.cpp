/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bv_refinement.h"

#ifdef DEBUG
#include <iostream>
#endif

#include <util/std_expr.h>
#include <util/find_symbols.h>

#include <solvers/sat/satcheck.h>

/// generate array constraints
void bv_refinementt::finish_eager_conversion_arrays()
{
  collect_indices();
  // at this point all indices should in the index set

  // just build the data structure
  update_index_map(true);

  // we don't actually add any constraints
  lazy_arrays=config_.refine_arrays;
  add_array_constraints();
  freeze_lazy_constraints();
}

/// check whether counterexample is spurious
void bv_refinementt::arrays_overapproximated()
{
  if(!config_.refine_arrays)
    return;

  unsigned nb_active=0;

  // Evaluate all lazy constraints while the solver is still in SAT state.
  // We must not interleave get_value() calls with modifications to the
  // main solver (prop) because some SAT solvers (e.g., CaDiCaL) only
  // permit reading model values while in the satisfied state, and adding
  // clauses invalidates that state.
  struct evaluated_constraintt
  {
    exprt constraint;
    exprt simplified;
    std::list<lazy_constraintt>::iterator list_it;
  };
  std::vector<evaluated_constraintt> to_check;
  to_check.reserve(lazy_array_constraints.size());

  for(auto it = lazy_array_constraints.begin();
      it != lazy_array_constraints.end();
      ++it)
  {
    const exprt &current = it->lazy;

    // some minor simplifications
    // check if they are worth having
    if(current.id()==ID_implies)
    {
      implies_exprt imp=to_implies_expr(current);
      exprt implies_simplified = get_value(imp.op0());
      if(implies_simplified==false_exprt())
      {
        continue;
      }
    }

    if(current.id()==ID_or)
    {
      or_exprt orexp=to_or_expr(current);
      INVARIANT(
        orexp.operands().size() == 2, "only treats the case of a binary or");
      exprt o1 = get_value(orexp.op0());
      exprt o2 = get_value(orexp.op1());
      if(o1==true_exprt() || o2 == true_exprt())
      {
        continue;
      }
    }

    to_check.push_back({current, get_value(current), it});
  }

  // Now check each evaluated constraint using a local solver and activate
  // violated ones. This phase may modify the main solver (prop).
  for(auto &entry : to_check)
  {
    satcheck_no_simplifiert sat_check{log.get_message_handler()};
    bv_pointerst solver{ns, sat_check, log.get_message_handler()};
    solver.unbounded_array = bv_pointerst::unbounded_arrayt::U_ALL;

    solver << entry.simplified;

    switch(static_cast<decision_proceduret::resultt>(sat_check.prop_solve()))
    {
    case decision_proceduret::resultt::D_SATISFIABLE:
      break;
    case decision_proceduret::resultt::D_UNSATISFIABLE:
      prop.l_set_to_true(convert(entry.constraint));
      nb_active++;
      lazy_array_constraints.erase(entry.list_it);
      break;
    case decision_proceduret::resultt::D_ERROR:
      INVARIANT(false, "error in array over approximation check");
    }
  }

  log.debug() << "BV-Refinement: " << nb_active
              << " array expressions become active" << messaget::eom;
  log.debug() << "BV-Refinement: " << lazy_array_constraints.size()
              << " inactive array expressions" << messaget::eom;
  if(nb_active > 0)
    progress=true;
}


/// freeze symbols for incremental solving
void bv_refinementt::freeze_lazy_constraints()
{
  if(!lazy_arrays)
    return;

  for(const auto &constraint : lazy_array_constraints)
  {
    // Freeze all symbols in the constraint
    for(const auto &symbol : find_symbols(constraint.lazy))
    {
      if(!bv_width.get_width_opt(symbol.type()).has_value())
        continue;
      const bvt bv=convert_bv(symbol);
      for(const auto &literal : bv)
        if(!literal.is_constant())
          prop.set_frozen(literal);
    }

    // Also freeze the full constraint literal and its sub-expressions
    // so that convert() during refinement does not hit eliminated
    // variables.
    literalt constraint_lit = convert(constraint.lazy);
    if(!constraint_lit.is_constant())
      prop.set_frozen(constraint_lit);
  }
}
