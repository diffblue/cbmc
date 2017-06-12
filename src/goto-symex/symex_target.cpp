/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "symex_target.h"

bool operator<(
  const symex_targett::sourcet &a,
  const symex_targett::sourcet &b)
{
  if(a.thread_nr==b.thread_nr)
    return a.pc < b.pc;
  else
    return a.thread_nr < b.thread_nr;
}
