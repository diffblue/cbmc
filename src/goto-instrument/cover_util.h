/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Coverage Instrumentation Utilities

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_UTIL_H
#define CPROVER_GOTO_INSTRUMENT_COVER_UTIL_H

#include <goto-programs/goto_program.h>

bool is_condition(const exprt &src);

void collect_conditions_rec(const exprt &src, std::set<exprt> &dest);

std::set<exprt> collect_conditions(const exprt &src);

std::set<exprt> collect_conditions(const goto_programt::const_targett t);

void collect_operands(const exprt &src, std::vector<exprt> &dest);

void collect_decisions_rec(const exprt &src, std::set<exprt> &dest);

std::set<exprt> collect_decisions(const exprt &src);

std::set<exprt> collect_decisions(const goto_programt::const_targett t);

#endif // CPROVER_GOTO_INSTRUMENT_COVER_UTIL_H
