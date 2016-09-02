/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

#ifndef CPROVER_COVER_H
#define CPROVER_COVER_H

#include <goto-programs/goto_model.h>

enum class coverage_criteriont {
  LOCATION, BRANCH, DECISION, CONDITION,
  PATH, MCDC, ASSERTION, COVER };

void set_existing_goals(std::string goal);

void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_programt &goto_program,
  coverage_criteriont);

void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  coverage_criteriont);

#endif
