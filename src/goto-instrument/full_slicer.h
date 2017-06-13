/*******************************************************************\

Module: Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_FULL_SLICER_H
#define CPROVER_GOTO_INSTRUMENT_FULL_SLICER_H

#include <goto-programs/goto_functions.h>

void full_slicer(
  goto_functionst &goto_functions,
  const namespacet &ns);

void property_slicer(
  goto_functionst &goto_functions,
  const namespacet &ns,
  const std::list<std::string> &properties);

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

#endif // CPROVER_GOTO_INSTRUMENT_FULL_SLICER_H
