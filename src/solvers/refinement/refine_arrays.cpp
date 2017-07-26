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
#if 0
  collect_indices();
  // at this point all indices should in the index set

  // just build the data structure
  update_index_map(true);

  // we don't actually add any constraints
  lazy_arrays=config_.refine_arrays;
  add_array_constraints();
  freeze_lazy_constraints();
#endif
}

/// check whether counterexample is spurious
void bv_refinementt::arrays_overapproximated()
{
#if 0
  if(!config_.refine_arrays)
    return;

  unsigned nb_active=0;

  std::list<lazy_constraintt>::iterator it=lazy_array_constraints.begin();
  while(it!=lazy_array_constraints.end())
  {
    satcheck_no_simplifiert sat_check{log.get_message_handler()};
    bv_pointerst solver{ns, sat_check, log.get_message_handler()};
    solver.unbounded_array=bv_pointerst::unbounded_arrayt::U_ALL;

    exprt current=(*it).lazy;

    // some minor simplifications
    // check if they are worth having
    if(current.id()==ID_implies)
    {
      implies_exprt imp=to_implies_expr(current);
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
        orexp.operands().size() == 2, "only treats the case of a binary or");
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
#endif
}

/// freeze symbols for incremental solving
void bv_refinementt::freeze_lazy_constraints()
{
#if 0
  if(!lazy_arrays)
    return;

  for(const auto &constraint : lazy_array_constraints)
  {
    for(const auto &symbol : find_symbols(constraint.lazy))
    {
      const bvt bv=convert_bv(symbol);
      for(const auto &literal : bv)
        if(!literal.is_constant())
          prop.set_frozen(literal);
    }
  }
#endif
}
