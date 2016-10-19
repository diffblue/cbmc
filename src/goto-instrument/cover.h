/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

#ifndef CPROVER_COVER_H
#define CPROVER_COVER_H

#include <goto-programs/goto_model.h>

class coverage_goals
{
public:
	void set_goals(std::string goal);
	const bool get_goals(const char* goal);

private:
	std::vector<std::string> existing_goals;
};

enum class coverage_criteriont {
  LOCATION, BRANCH, DECISION, CONDITION,
  PATH, MCDC, ASSERTION, COVER };

void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_programt &goto_program,
  coverage_criteriont,
  coverage_goals &goals);

void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  coverage_criteriont,
  coverage_goals &goals);

#endif
