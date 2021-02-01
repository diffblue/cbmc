/*******************************************************************\

Module: Process a Goto Program

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_PROCESS_GOTO_PROGRAM_H
#define CPROVER_GOTO_PROGRAMS_PROCESS_GOTO_PROGRAM_H

class goto_modelt;
class optionst;
class messaget;

/// Common processing and simplification of goto_programts.
/// This includes removing a number of more complex types
/// (vectors, complex, etc.) and constructs
/// (returns, function pointers, etc.).
/// This is can be used after initialize_goto_model but before
/// analysis.  It is not mandatory but is used by most tools.
bool process_goto_program(
  goto_modelt &goto_model,
  const optionst &options,
  messaget &log);

#endif // CPROVER_GOTO_PROGRAMS_PROCESS_GOTO_PROGRAM_H
