/*******************************************************************\

Module: Initialize command line arguments

Author: Michael Tautschnig

Date: April 2016

\*******************************************************************/

/// \file
/// Initialize command line arguments

#ifndef CPROVER_GOTO_INSTRUMENT_MODEL_ARGC_ARGV_H
#define CPROVER_GOTO_INSTRUMENT_MODEL_ARGC_ARGV_H

class goto_modelt;
class message_handlert;

bool model_argc_argv(
  goto_modelt &,
  unsigned max_argc,
  message_handlert &);

#endif // CPROVER_GOTO_INSTRUMENT_MODEL_ARGC_ARGV_H
