/*******************************************************************\

Module: List all unreachable instructions

Author: Michael Tautschnig

Date: April 2016

\*******************************************************************/

/// \file
/// List all unreachable instructions

#ifndef CPROVER_GOTO_ANALYZER_UNREACHABLE_INSTRUCTIONS_H
#define CPROVER_GOTO_ANALYZER_UNREACHABLE_INSTRUCTIONS_H

#include <iosfwd>

class ai_baset;
class goto_modelt;
class optionst;

void unreachable_instructions(
  const goto_modelt &,
  const bool json,
  std::ostream &os);

void unreachable_functions(
  const goto_modelt &,
  const bool json,
  std::ostream &os);

void reachable_functions(
  const goto_modelt &,
  const bool json,
  std::ostream &os);

bool static_unreachable_instructions(
  const goto_modelt &,
  const ai_baset &,
  const optionst &,
  std::ostream &);

bool static_unreachable_functions(
  const goto_modelt &,
  const ai_baset &,
  const optionst &,
  std::ostream &);

bool static_reachable_functions(
  const goto_modelt &,
  const ai_baset &,
  const optionst &,
  std::ostream &);

#endif // CPROVER_GOTO_ANALYZER_UNREACHABLE_INSTRUCTIONS_H
