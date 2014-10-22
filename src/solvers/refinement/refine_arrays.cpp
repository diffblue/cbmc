/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>

#include "bv_refinement.h"

/*******************************************************************\

Function: bv_refinementt::post_process_arrays

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::post_process_arrays()
{
  // just build the data structure
  build_index_map();

  // we don't actually add any constraints
}

/*******************************************************************\

Function: bv_refinementt::arrays_overapproximated

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::arrays_overapproximated()
{
  // build index_map with values
  index_mapt value_index_map;

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

