/*******************************************************************\

Module: Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Slicing

#ifndef CPROVER_GOTO_INSTRUMENT_FULL_SLICER_H
#define CPROVER_GOTO_INSTRUMENT_FULL_SLICER_H

#include <goto-programs/goto_program.h>

class goto_functionst;
class goto_modelt;
class message_handlert;

void full_slicer(goto_functionst &, const namespacet &, message_handlert &);

void full_slicer(goto_modelt &, message_handlert &);

void property_slicer(
  goto_functionst &,
  const namespacet &,
  const std::list<std::string> &properties,
  message_handlert &);

void property_slicer(
  goto_modelt &,
  const std::list<std::string> &properties,
  message_handlert &);

class slicing_criteriont
{
public:
  virtual ~slicing_criteriont();
  virtual bool operator()(
    const irep_idt &function_id,
    goto_programt::const_targett) const = 0;
};

void full_slicer(
  goto_functionst &goto_functions,
  const namespacet &ns,
  const slicing_criteriont &criterion,
  message_handlert &);

#endif // CPROVER_GOTO_INSTRUMENT_FULL_SLICER_H
