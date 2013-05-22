/*******************************************************************\

Module: Interval Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>

#include "interval_domain.h"

/*******************************************************************\

Function: interval_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interval_domaint::output(
  const namespacet &ns,
  std::ostream &out) const
{
  
}

/*******************************************************************\

Function: interval_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interval_domaint::transform(
  const namespacet &ns,
  locationt from,
  locationt to)
{
}

/*******************************************************************\

Function: interval_domaint::merge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool interval_domaint::merge(const interval_domaint &b)
{
  return false;
}

/*******************************************************************\

Function: interval_domaint::make_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt interval_domaint::make_expression() const
{
  exprt::operandst conjuncts;

  for(int_mapt::const_iterator it=int_map.begin();
      it!=int_map.end(); it++)
  {
    //if(
  }

  for(float_mapt::const_iterator it=float_map.begin();
      it!=float_map.end(); it++)
  {
  }
  
  return true_exprt();
}
