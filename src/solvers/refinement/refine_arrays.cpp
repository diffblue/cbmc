/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bv_refinement.h"

#ifdef DEBUG
#include <iostream>
#include <langapi/language_util.h>
#endif

#include <util/std_expr.h>
#include <util/find_symbols.h>

#include <solvers/refinement/string_refinement_invariant.h>
#include <solvers/sat/satcheck.h>

/// generate array constraints
void bv_refinementt::post_process_arrays()
{
  collect_indices();
  // at this point all indices should in the index set

  // just build the data structure
  update_index_map(true);

  // we don't actually add any constraints
  lazy_arrays=do_array_refinement;
  add_array_constraints();
  freeze_lazy_constraints();
}

/// check whether counterexample is spurious
void bv_refinementt::arrays_overapproximated()
{
  if(!do_array_refinement)
    return;

  unsigned nb_active=0;

  std::list<lazy_constraintt>::iterator it=lazy_array_constraints.begin();
  while(it!=lazy_array_constraints.end())
  {
    satcheck_no_simplifiert sat_check;
    bv_pointerst solver(ns, sat_check);
    solver.unbounded_array=bv_pointerst::unbounded_arrayt::U_ALL;

    exprt current=(*it).lazy;

    // some minor simplifications
    // check if they are worth having
    if(current.id()==ID_implies)
    {
      implies_exprt imp=to_implies_expr(current);
      DATA_INVARIANT(
        imp.operands().size()==2,
        string_refinement_invariantt("implies must have two operands"));
      exprt implies_simplified=get(imp.op0());
      if(implies_simplified==false_exprt())
      {
        ++it;
        continue;
      }
    }

    if(current.id()==ID_or)
    {
      or_exprt orexp=to_or_expr(current);
      INVARIANT(
        orexp.operands().size()==2,
        string_refinement_invariantt("only treats the case of a binary or"));
      exprt o1=get(orexp.op0());
      exprt o2=get(orexp.op1());
      if(o1==true_exprt() || o2 == true_exprt())
      {
        ++it;
        continue;
      }
    }

    exprt simplified=get(current);
    solver << simplified;

    switch(static_cast<decision_proceduret::resultt>(sat_check.prop_solve()))
    {
    case decision_proceduret::resultt::D_SATISFIABLE:
      ++it;
      break;
    case decision_proceduret::resultt::D_UNSATISFIABLE:
      prop.l_set_to_true(convert(current));
      nb_active++;
      lazy_array_constraints.erase(it++);
      break;
    default:
      error() << "error in array over approximation check" << eom;
      INVARIANT(
        false,
        string_refinement_invariantt("error in array over approximation "
          "check"));
      // Placeholder to tell the compiler we bail
      throw 0;
    }
  }

  debug() << "BV-Refinement: " << nb_active
          << " array expressions become active" << eom;
  debug() << "BV-Refinement: " << lazy_array_constraints.size()
          << " inactive array expressions" << eom;
  if(nb_active > 0)
    progress=true;
}


/// freeze symbols for incremental solving
void bv_refinementt::freeze_lazy_constraints()
{
  if(!lazy_arrays)
    return;

  for(std::list<lazy_constraintt>::iterator
        l_it=lazy_array_constraints.begin();
      l_it!=lazy_array_constraints.end(); ++l_it)
  {
    std::set<symbol_exprt> symbols;
    find_symbols(l_it->lazy, symbols);
    for(std::set<symbol_exprt>::const_iterator it=symbols.begin();
        it!=symbols.end(); ++it)
    {
      bvt bv=convert_bv(l_it->lazy);
      forall_literals(b_it, bv)
        if(!b_it->is_constant())
          prop.set_frozen(*b_it);
    }
  }
}
