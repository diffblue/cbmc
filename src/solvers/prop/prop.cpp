/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "prop.h"

/// asserts a==b in the propositional formula
void propt::set_equal(literalt a, literalt b)
{
  if(b.is_constant())
  {
    if(b.is_true())
      lcnf({a});
    else
      lcnf({!a});

    return;
  }

  lcnf(a, !b);
  lcnf(!a, b);
}

/// generates a bitvector of given width with new variables
/// \return bitvector
bvt propt::new_variables(std::size_t width)
{
  bvt result;
  result.reserve(width);
  for(std::size_t i=0; i<width; i++)
    result.push_back(new_variable());
  return result;
}

propt::resultt propt::prop_solve()
{
  static const bvt empty_assumptions;
  ++number_of_solver_calls;
  return do_prop_solve(empty_assumptions);
}

propt::resultt propt::prop_solve(const bvt &assumptions)
{
  ++number_of_solver_calls;
  return do_prop_solve(assumptions);
}

std::size_t propt::get_number_of_solver_calls() const
{
  return number_of_solver_calls;
}
