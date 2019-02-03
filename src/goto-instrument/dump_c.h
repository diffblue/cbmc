/*******************************************************************\

Module: Dump C from Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Dump C from Goto Program

#ifndef CPROVER_GOTO_INSTRUMENT_DUMP_C_H
#define CPROVER_GOTO_INSTRUMENT_DUMP_C_H

#include <goto-programs/goto_functions.h>

class message_handlert;

void dump_c(
  const goto_functionst &src,
  const bool use_system_headers,
  const bool use_all_headers,
  const bool include_harness,
  const namespacet &ns,
  std::ostream &out,
  message_handlert &message_handler);

void dump_cpp(
  const goto_functionst &src,
  const bool use_system_headers,
  const bool use_all_headers,
  const bool include_harness,
  const namespacet &ns,
  std::ostream &out,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_INSTRUMENT_DUMP_C_H
