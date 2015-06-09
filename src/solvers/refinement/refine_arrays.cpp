/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>

#include "bv_refinement.h"
#include <solvers/sat/satcheck.h>

/*******************************************************************\

Function: bv_refinementt::post_process_arrays

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::post_process_arrays()
{
  collect_indices();
  // at this point all indices should in the index set
  
  // just build the data structure
  update_index_map();

  // we don't actually add any constraints
  lazy_arrays = do_array_refinement;
  add_array_constraints();
}

/*******************************************************************\

Function: bv_refinementt::arrays_overapproximated

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::arrays_overapproximated()
{
  if(!lazy_arrays) return;
  
  unsigned nb_active = 0;

  std::list<lazy_constraintt>::iterator it = lazy_array_constraints.begin();
  while(it != lazy_array_constraints.end())
  {
    satcheck_minisat_no_simplifiert sat_check;
    bv_pointerst solver(ns,sat_check);

    exprt current = (*it).lazy;

    // some minor simplifications
    // check if they are worth having
    if (current.id() == ID_implies)
    {
      implies_exprt imp = to_implies_expr(current);
      assert (imp.operands().size() == 2);
      exprt implies_simplified = get(imp.op0());
      if (implies_simplified == false_exprt()){
	      ++it;
	      continue;
      }
    }

    if (current.id() == ID_or)
    {
      or_exprt orexp = to_or_expr(current);
      assert (orexp.operands().size() == 2);
      exprt o1 = get(orexp.op0());
      exprt o2 = get(orexp.op1());
      if (o1 == true_exprt() || o2 == true_exprt())
      {
	      ++it;
	      continue;
      }
    }

    exprt simplified = get(current);
    solver << simplified;

    switch(sat_check.prop_solve())
    {
      case decision_proceduret::D_SATISFIABLE:
        ++it;
	      break; 
      case decision_proceduret::D_UNSATISFIABLE:
        prop.l_set_to_true(convert(current));
        nb_active++;
        lazy_array_constraints.erase(it++);
	      break;
      default:
	assert(false);
    }

  }

  debug() << "BV-Refinement: " << nb_active 
	  << " array expressions become active" << eom;
  debug() << "BV-Refinement: " << lazy_array_constraints.size() 
	  << " inactive array expressions" << eom;
  if (nb_active > 0)
    progress = true;

  #if 0
  // iterate over *roots*
  for(unsigned i=0; i<arrays.size(); i++)
  {
    if(!arrays.is_root_number(i)) continue;

    unsigned root_number=arrays.find_number(i);
    assert(root_number!=i);

    index_sett &root_index_set=index_map[root_number];
    index_sett &index_set=index_map[i];

    root_index_set.insert(index_set.begin(), index_set.end());
  }  

  // check constraints for if, with, array_of
  for(unsigned i=0; i<arrays.size(); i++)
    add_array_constraints(
      index_map[arrays.find_number(i)],
      arrays[i]);

  // check constraints for equalities
  for(array_equalitiest::const_iterator it=
      array_equalities.begin();
      it!=array_equalities.end();
      it++)
    add_array_constraints(
      index_map[arrays.find_number(it->f1)],
      *it);
  #endif
}

