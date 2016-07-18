/*******************************************************************\

Module: Flow Insensitive Static Analysis

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger, Peter Schrammel

\*******************************************************************/

#include <cassert>

#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/expr_util.h>

#include "flow_insensitive_analysis.h"

/*******************************************************************\

Function: flow_insensitive_analysis_baset::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void flow_insensitive_analysis_baset::output(
  const namespacet &ns,
  const goto_programt &goto_program,
  const irep_idt &identifier,
  std::ostream &out) const
{
  get_state().output(out, *this, ns);  
}


/*******************************************************************\

Function: flow_insensitive_analysis_baset::entry_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void flow_insensitive_analysis_baset::entry_state(const goto_programt &goto_program)
{
  entry_location = goto_program.instructions.begin();
  }

