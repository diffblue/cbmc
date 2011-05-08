/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "symex_target.h"

/*******************************************************************\

Function: operator <

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator < (const symex_targett::sourcet &a, const symex_targett::sourcet &b)
{
  if(a.thread_nr < b.thread_nr) return true;
  return a.pc < b.pc;
}
