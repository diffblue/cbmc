/*******************************************************************\

Module: Count effective lines of code

Author: Michael Tautschnig

Date: December 2012

\*******************************************************************/

/// \file
/// Count effective lines of code

#ifndef CPROVER_GOTO_INSTRUMENT_COUNT_ELOC_H
#define CPROVER_GOTO_INSTRUMENT_COUNT_ELOC_H

class goto_modelt;

void count_eloc(const goto_modelt &);
void list_eloc(const goto_modelt &);
void print_path_lengths(const goto_modelt &);
void print_global_state_size(const goto_modelt &);

#define OPT_GOTO_PROGRAM_STATS                                                 \
  "(count-eloc)"                                                               \
  "(list-eloc)"                                                                \
  "(print-global-state-size)"                                                  \
  "(print-path-lengths)"

#define HELP_GOTO_PROGRAM_STATS                                                \
  " --count-eloc                 count effective lines of code\n"              \
  " --list-eloc                  list full path names of lines "               \
  "containing code\n"                                                          \
  " --print-global-state-size    count the total number of bits of global "    \
  "objects\n"                                                                  \
  " --print-path-lengths         print statistics about control-flow graph "   \
  "paths\n"

#endif // CPROVER_GOTO_INSTRUMENT_COUNT_ELOC_H
