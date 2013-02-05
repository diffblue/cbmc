/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "goto_symex.h"

/*******************************************************************\

Function: goto_symext::symex_atomic_begin

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_atomic_begin(statet &state)
{
  state.atomic_section_count++;
}

/*******************************************************************\

Function: goto_symext::symex_atomic_end

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_atomic_end(statet &state)
{
  if(state.atomic_section_count==0)
    throw "ATOMIC_END unmatched";
  state.atomic_section_count--;
}
