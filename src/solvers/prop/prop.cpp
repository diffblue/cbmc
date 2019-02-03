/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "prop.h"

/// asserts a==b in the propositional formula
void propt::set_equal(literalt a, literalt b)
{
  lcnf(a, !b);
  lcnf(!a, b);
}

/// generates a bitvector of given width with new variables
/// \return bitvector
bvt propt::new_variables(std::size_t width)
{
  bvt result;
  result.resize(width);
  for(std::size_t i=0; i<width; i++)
    result[i]=new_variable();
  return result;
}

propt::resultt propt::prop_solve()
{
  return do_prop_solve();
}
