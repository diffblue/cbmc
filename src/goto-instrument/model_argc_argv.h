/*******************************************************************\

Module: Initialize command line arguments

Author: Michael Tautschnig

Date: April 2016

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_MODEL_ARGC_ARGV_H
#define CPROVER_GOTO_INSTRUMENT_MODEL_ARGC_ARGV_H

class goto_functionst;
class message_handlert;
class symbol_tablet;

bool model_argc_argv(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  unsigned max_argc,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_INSTRUMENT_MODEL_ARGC_ARGV_H
