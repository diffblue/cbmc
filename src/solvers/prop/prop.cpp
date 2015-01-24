/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "prop.h"

/*******************************************************************\

Function: propt::set_equal

  Inputs:

 Outputs:

 Purpose: asserts a==b in the propositional formula

\*******************************************************************/

void propt::set_equal(literalt a, literalt b)
{
  lcnf(a, !b);
  lcnf(!a, b);
}

/*******************************************************************\

Function: propt::set_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void propt::set_assignment(literalt a, bool value)
{
  assert(false);
}

/*******************************************************************\

Function: propt::copy_assignment_from

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void propt::copy_assignment_from(const propt &src)
{
  assert(false);
}

/*******************************************************************\

Function: propt::is_in_conflict

  Inputs:

 Outputs: true iff the given literal is part of the final conflict

 Purpose:  

\*******************************************************************/

bool propt::is_in_conflict(literalt l) const
{
  assert(false);
  return false;
}

/*******************************************************************\

Function: propt::new_variables

  Inputs: width

 Outputs: bitvector 

 Purpose: generates a bitvector of given width with new variables 

\*******************************************************************/

bvt propt::new_variables(unsigned width)
{
  bvt result;
  result.resize(width);
  for(unsigned i=0; i<width; i++)
    result[i]=new_variable();
  return result;
}


