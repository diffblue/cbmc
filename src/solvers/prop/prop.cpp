/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "prop.h"

/// asserts a==b in the propositional formula
void propt::set_equal(literalt a, literalt b)
{
  lcnf(a, !b);
  lcnf(!a, b);
}

void propt::set_assignment(literalt a, bool value)
{
  assert(false);
}

void propt::copy_assignment_from(const propt &src)
{
  assert(false);
}

/// \return true iff the given literal is part of the final conflict
bool propt::is_in_conflict(literalt l) const
{
  assert(false);
  return false;
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
