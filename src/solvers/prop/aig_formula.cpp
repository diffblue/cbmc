/*******************************************************************\

Module: AND-Inverter Graph Formula

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "aig_formula.h"

#if 0
/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &operator << (std::ostream &out, const aig_formulat &f)
{
  return out;
}

/*******************************************************************\

Function: aig_formulat::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt aig_formulat::convert(propt &dest) const
{
  if(l.is_constant()) return l;

  std::vector<literalt> literals;

  aig.convert(dest, literals);

  unsigned v=l.var_no();

  assert(v<literals.size());

  return literals[v].cond_negation(l.sign());
}

/*******************************************************************\

Function: aig_formulat::add_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void aig_formulat::add_variables(propt &dest) const
{
  aig.add_variables(dest);
}
#endif
