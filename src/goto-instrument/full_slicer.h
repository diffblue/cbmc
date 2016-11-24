/*******************************************************************\

Module: Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_FULL_SLICER_H
#define CPROVER_GOTO_PROGRAMS_FULL_SLICER_H

#include <goto-programs/goto_functions.h>

void full_slicer(
  goto_functionst &goto_functions,
  const namespacet &ns);

class slicing_criteriont
{
public:
  virtual ~slicing_criteriont();
  virtual bool operator()(goto_programt::const_targett)=0;
};

void full_slicer(
  goto_functionst &goto_functions,
  const namespacet &ns,
  slicing_criteriont &criterion);

#endif
