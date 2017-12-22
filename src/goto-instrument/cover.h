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
#include <util/cmdline.h>

class message_handlert;
class messaget;

enum class coverage_criteriont
{
  LOCATION, BRANCH, DECISION, CONDITION,
  PATH, MCDC, ASSERTION, COVER };

void instrument_cover_goals(
  const symbol_tablet &,
  goto_functionst &,
  coverage_criteriont,
  message_handlert &message_handler,
  bool function_only=false);

void instrument_cover_goals(
  const symbol_tablet &,
  goto_programt &,
  coverage_criteriont,
  message_handlert &message_handler,
  bool function_only=false);

void instrument_cover_goals(
  const symbol_tablet &,
  goto_functionst &,
  coverage_criteriont,
  message_handlert &message_handler,
  bool function_only=false,
  bool ignore_trivial=false,
  const std::string &cover_inclue_pattern="");

void instrument_cover_goals(
  const symbol_tablet &,
  goto_programt &,
  coverage_criteriont,
  message_handlert &message_handler,
  bool function_only=false,
  bool ignore_trivial=false);

bool instrument_cover_goals(
  const cmdlinet &,
  const symbol_tablet &,
  goto_functionst &,
  message_handlert &);

bool instrument_cover_goals(
  const cmdlinet &,
  goto_modelt &,
  message_handlert &);

#endif // CPROVER_GOTO_INSTRUMENT_COVER_H
