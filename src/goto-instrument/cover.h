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

class coverage_goalst
{
public:
  static bool get_coverage_goals(
    const std::string &coverage,
    message_handlert &message_handler,
    coverage_goalst &goals);
  void add_goal(source_locationt goal);
  bool is_existing_goal(source_locationt source_location) const;

private:
  std::vector<source_locationt> existing_goals;
};

enum class coverage_criteriont
{
  LOCATION, BRANCH, DECISION, CONDITION,
  PATH, MCDC, ASSERTION, COVER };

bool consider_goals(
  const goto_programt &goto_program,
  coverage_goalst &goals);

void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  coverage_criteriont,
  bool function_only=false);

void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_programt &goto_program,
  coverage_criteriont,
  bool function_only=false);

void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  coverage_criteriont,
  const coverage_goalst &goals,
  bool function_only=false,
  bool ignore_trivial=false);

void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_programt &goto_program,
  coverage_criteriont,
  const coverage_goalst &goals,
  bool function_only=false,
  bool ignore_trivial=false);

#endif // CPROVER_GOTO_INSTRUMENT_COVER_H
