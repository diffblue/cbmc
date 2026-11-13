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

static propt::statust status_from_result(propt::resultt result)
{
  switch(result)
  {
  case propt::resultt::P_SATISFIABLE:
    return propt::statust::SAT;
  case propt::resultt::P_UNSATISFIABLE:
    return propt::statust::UNSAT;
  case propt::resultt::P_ERROR:
    return propt::statust::ERROR;
  }
  UNREACHABLE;
}

propt::resultt propt::prop_solve()
{
  static const bvt empty_assumptions;
  ++number_of_solver_calls;
  // Some do_prop_solve() implementations may throw (e.g., on solver
  // interruption). Ensure solver_state is set to ERROR in that case so that
  // l_get()/is_in_conflict() preconditions will fail.
  try
  {
    auto result = do_prop_solve(empty_assumptions);
    solver_state = status_from_result(result);
    return result;
  }
  catch(...)
  {
    solver_state = statust::ERROR;
    throw;
  }
}

propt::resultt propt::prop_solve(const bvt &assumptions)
{
  ++number_of_solver_calls;
  try
  {
    auto result = do_prop_solve(assumptions);
    solver_state = status_from_result(result);
    return result;
  }
  catch(...)
  {
    solver_state = statust::ERROR;
    throw;
  }
}

std::size_t propt::get_number_of_solver_calls() const
{
  return number_of_solver_calls;
}
