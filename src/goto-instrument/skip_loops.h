/*******************************************************************\

Module: Skip over selected loops by adding gotos

Author: Michael Tautschnig

Date: January 2016

\*******************************************************************/

/// \file
/// Skip over selected loops by adding gotos

#ifndef CPROVER_GOTO_INSTRUMENT_SKIP_LOOPS_H
#define CPROVER_GOTO_INSTRUMENT_SKIP_LOOPS_H

#include <string>

class goto_functionst;
class message_handlert;

bool skip_loops(
  goto_functionst &goto_functions,
  const std::string &loop_ids,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_INSTRUMENT_SKIP_LOOPS_H
