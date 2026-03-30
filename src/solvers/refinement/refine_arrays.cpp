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
template <typename bv_pointers_baset>
void bv_refinementt<bv_pointers_baset>::finish_eager_conversion_arrays()
{
  this->collect_indices();
  // at this point all indices should in the index set

  // just build the data structure
  this->update_index_map(true);

  // we don't actually add any constraints
  this->lazy_arrays = config_.refine_arrays;
  this->add_array_constraints();
  freeze_lazy_constraints();
}

/// check whether counterexample is spurious
template <typename bv_pointers_baset>
void bv_refinementt<bv_pointers_baset>::arrays_overapproximated()
{
  if(!config_.refine_arrays)
    return;

  unsigned nb_active=0;

  // Evaluate all lazy constraints while the solver is still in SAT state.
  // We must not interleave this->get_value() calls with modifications to the
  // main solver (prop) because some SAT solvers (e.g., CaDiCaL) only
  // permit reading model values while in the satisfied state, and adding
  // clauses invalidates that state.
  // Collect constraints to check with their iterators
  using list_iterator_t = decltype(this->lazy_array_constraints.begin());
  struct evaluated_constraintt
  {
    exprt constraint;
    exprt simplified;
    list_iterator_t list_it;
  };
  std::vector<evaluated_constraintt> to_check;
  to_check.reserve(this->lazy_array_constraints.size());

  for(auto it = this->lazy_array_constraints.begin();
      it != this->lazy_array_constraints.end();
      ++it)
  {
    const exprt &current = it->lazy;

    // some minor simplifications
    // check if they are worth having
    if(current.id()==ID_implies)
    {
      implies_exprt imp=to_implies_expr(current);
      exprt implies_simplified = this->get_value(imp.op0());
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
      exprt o1 = this->get_value(orexp.op0());
      exprt o2 = this->get_value(orexp.op1());
      if(o1==true_exprt() || o2 == true_exprt())
      {
        continue;
      }
    }

    to_check.push_back({current, this->get_value(current), it});
  }

  // Now check each evaluated constraint using a local solver and activate
  // violated ones. This phase may modify the main solver (prop).
  for(auto &entry : to_check)
  {
    satcheck_no_simplifiert sat_check{this->log.get_message_handler()};
    bv_pointerst solver{this->ns, sat_check, this->log.get_message_handler()};
    solver.unbounded_array = bv_pointerst::unbounded_arrayt::U_ALL;

    solver << entry.simplified;

    switch(static_cast<decision_proceduret::resultt>(sat_check.prop_solve()))
    {
    case decision_proceduret::resultt::D_SATISFIABLE:
      break;
    case decision_proceduret::resultt::D_UNSATISFIABLE:
      this->prop.l_set_to_true(this->convert(entry.constraint));
      nb_active++;
      this->lazy_array_constraints.erase(entry.list_it);
      break;
    case decision_proceduret::resultt::D_ERROR:
      INVARIANT(false, "error in array over approximation check");
    }
  }

  this->log.debug() << "BV-Refinement: " << nb_active
                    << " array expressions become active" << messaget::eom;
  this->log.debug() << "BV-Refinement: " << this->lazy_array_constraints.size()
                    << " inactive array expressions" << messaget::eom;
  if(nb_active > 0)
    progress=true;
}


/// freeze symbols for incremental solving
template <typename bv_pointers_baset>
void bv_refinementt<bv_pointers_baset>::freeze_lazy_constraints()
{
  if(!this->lazy_arrays)
    return;

  for(const auto &constraint : this->lazy_array_constraints)
  {
    // Freeze all symbols in the constraint
    for(const auto &symbol : find_symbols(constraint.lazy))
    {
      if(!this->bv_width.get_width_opt(symbol.type()).has_value())
        continue;
      const bvt bv = this->convert_bv(symbol);
      for(const auto &literal : bv)
        if(!literal.is_constant())
          this->prop.set_frozen(literal);
    }

    // Also freeze the full constraint literal and its sub-expressions
    // so that this->convert() during refinement does not hit eliminated
    // variables.
    literalt constraint_lit = this->convert(constraint.lazy);
    if(!constraint_lit.is_constant())
      this->prop.set_frozen(constraint_lit);
  }
}

// Explicit instantiations
#include <solvers/flattening/bv_pointers_wide.h>

template class bv_refinementt<bv_pointerst>;
template class bv_refinementt<bv_pointers_widet>;
