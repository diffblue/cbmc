/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_H
#define CPROVER_GOTO_INSTRUMENT_COVER_H

#include <goto-programs/goto_model.h>

enum class coverage_criteriont {
  LOCATION, BRANCH, DECISION, CONDITION,
  PATH, MCDC, BOUNDARY, ASSERTION, COVER};

void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_programt &goto_program,
  const std::set<coverage_criteriont> &criteria);

void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  const std::set<coverage_criteriont> &criteria);

#endif // CPROVER_GOTO_INSTRUMENT_COVER_H
