/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

/// \file
/// Coverage Instrumentation

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_H
#define CPROVER_GOTO_INSTRUMENT_COVER_H

#include <goto-programs/goto_model.h>

class message_handlert;
class cmdlinet;
class optionst;

enum class coverage_criteriont
{
  LOCATION,
  BRANCH,
  DECISION,
  CONDITION,
  PATH,
  MCDC,
  ASSERTION,
  COVER // __CPROVER_cover(x) annotations
};

void instrument_cover_goals(
  const symbol_tablet &,
  goto_functionst &,
  coverage_criteriont,
  message_handlert &message_handler);

void instrument_cover_goals(
  const symbol_tablet &,
  goto_programt &,
  coverage_criteriont,
  message_handlert &message_handler);

void parse_cover_options(const cmdlinet &, optionst &);

bool instrument_cover_goals(
  const optionst &,
  const symbol_tablet &,
  goto_functionst &,
  message_handlert &);

bool instrument_cover_goals(
  const optionst &,
  goto_modelt &,
  message_handlert &);

#endif // CPROVER_GOTO_INSTRUMENT_COVER_H
