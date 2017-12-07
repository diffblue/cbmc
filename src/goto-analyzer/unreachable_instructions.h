/*******************************************************************\

Module: List all unreachable instructions

Author: Michael Tautschnig

Date: April 2016

\*******************************************************************/

/// \file
/// List all unreachable instructions

#ifndef CPROVER_GOTO_ANALYZER_UNREACHABLE_INSTRUCTIONS_H
#define CPROVER_GOTO_ANALYZER_UNREACHABLE_INSTRUCTIONS_H

#include <ostream>

#include <analyses/ai.h>

#include <util/options.h>
#include <util/message.h>

class goto_modelt;

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
  message_handlert &,
  std::ostream &);

bool static_unreachable_functions(
  const goto_modelt &,
  const ai_baset &,
  const optionst &,
  message_handlert &,
  std::ostream &);

bool static_reachable_functions(
  const goto_modelt &,
  const ai_baset &,
  const optionst &,
  message_handlert &,
  std::ostream &);

#endif // CPROVER_GOTO_ANALYZER_UNREACHABLE_INSTRUCTIONS_H
