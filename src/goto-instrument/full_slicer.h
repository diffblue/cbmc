/*******************************************************************\

Module: Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Slicing

#ifndef CPROVER_GOTO_INSTRUMENT_FULL_SLICER_H
#define CPROVER_GOTO_INSTRUMENT_FULL_SLICER_H

#include <goto-programs/goto_model.h>

void full_slicer(
  goto_functionst &,
  const namespacet &);

void full_slicer(goto_modelt &);

void property_slicer(
  goto_functionst &,
  const namespacet &,
  const std::list<std::string> &properties);

void property_slicer(
  goto_modelt &,
  const std::list<std::string> &properties);

class slicing_criteriont
{
public:
  virtual ~slicing_criteriont();
  virtual bool operator()(goto_programt::const_targett) const = 0;
};

void full_slicer(
  goto_functionst &goto_functions,
  const namespacet &ns,
  const slicing_criteriont &criterion);

#endif // CPROVER_GOTO_INSTRUMENT_FULL_SLICER_H
