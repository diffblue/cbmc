/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "static_analyser.h"



/*******************************************************************\

Function: static_analysert::show_intervals

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_analysert::show_intervals(
  const goto_modelt &goto_model,
  std::ostream &out)
{
  ait<interval_domaint> interval_analysis;

  if (constant_propagation)
    propagate_constants();

  interval_analysis(goto_model);
  interval_analysis.output(goto_model, out);
}
