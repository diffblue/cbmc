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
  bvt bv;
  bv.resize(2);
  bv[0]=a;
  bv[1]=lnot(b);
  lcnf(bv);
  
  bv[0]=lnot(a);
  bv[1]=b;
  lcnf(bv);
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

/*******************************************************************\

Function: propt::set_frozen

  Inputs: bitvector

 Outputs:

 Purpose: freezes all variables in the bitvector

\*******************************************************************/

void propt::set_frozen(bvt bv) 
{ 
  for(unsigned i=0; i<bv.size(); i++) 
    if(!bv[i].is_constant()) set_frozen(bv[i]); 
}


/*******************************************************************\

Function: propt::set_frozen

  Inputs:

 Outputs:

 Purpose: freezes the variables to be frozen and clears the set

\*******************************************************************/

void propt::set_frozen() 
{  
  for(variablest::const_iterator it = vars_to_be_frozen.begin();  
      it!=vars_to_be_frozen.end(); it++) 
  {
    set_frozen(literalt(*it,false));
  }
  vars_to_be_frozen.clear();
}

