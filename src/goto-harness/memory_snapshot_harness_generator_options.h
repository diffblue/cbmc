/******************************************************************\

Module: memory_snapshot_harness_generator_options

Author: Diffblue Ltd.

\******************************************************************/

#ifndef CPROVER_GOTO_HARNESS_MEMORY_SNAPSHOT_HARNESS_GENERATOR_OPTIONS_H
#define CPROVER_GOTO_HARNESS_MEMORY_SNAPSHOT_HARNESS_GENERATOR_OPTIONS_H

#include "common_harness_generator_options.h"

#define MEMORY_SNAPSHOT_HARNESS_SNAPSHOT_OPT "memory-snapshot"
#define MEMORY_SNAPSHOT_HARNESS_INITIAL_GOTO_LOC_OPT "initial-goto-location"
#define MEMORY_SNAPSHOT_HARNESS_INITIAL_SOURCE_LOC_OPT "initial-source-location"
#define MEMORY_SNAPSHOT_HARNESS_HAVOC_VARIABLES_OPT "havoc-variables"
#define MEMORY_SNAPSHOT_HARNESS_TREAT_POINTER_AS_ARRAY_OPT "pointer-as-array"
#define MEMORY_SNAPSHOT_HARNESS_ASSOCIATED_ARRAY_SIZE_OPT "size-of-array"

#define MEMORY_SNAPSHOT_HARNESS_GENERATOR_OPTIONS                              \
  "(" MEMORY_SNAPSHOT_HARNESS_SNAPSHOT_OPT                                     \
  "):"                                                                         \
  "(" MEMORY_SNAPSHOT_HARNESS_INITIAL_GOTO_LOC_OPT                             \
  "):"                                                                         \
  "(" MEMORY_SNAPSHOT_HARNESS_INITIAL_SOURCE_LOC_OPT                           \
  "):"                                                                         \
  "(" MEMORY_SNAPSHOT_HARNESS_HAVOC_VARIABLES_OPT                              \
  "):"                                                                         \
  "(" MEMORY_SNAPSHOT_HARNESS_TREAT_POINTER_AS_ARRAY_OPT                       \
  "):"                                                                         \
  "(" MEMORY_SNAPSHOT_HARNESS_ASSOCIATED_ARRAY_SIZE_OPT "):"

#define MEMORY_SNAPSHOT_HARNESS_GENERATOR_HELP                                 \
  "memory snapshot harness generator (--harness-type\n"                        \
  "  initialize-with-memory-snapshot):\n"                                      \
    << help_entry(                                                             \
         "--" MEMORY_SNAPSHOT_HARNESS_SNAPSHOT_OPT " <file>",                  \
         "initialize memory from JSON memory snapshot")                        \
    << help_entry(                                                             \
         "--" MEMORY_SNAPSHOT_HARNESS_INITIAL_GOTO_LOC_OPT " <func[:<n>]>",    \
         "use given function and location number as entry point")              \
    << help_entry(                                                             \
         "--" MEMORY_SNAPSHOT_HARNESS_INITIAL_SOURCE_LOC_OPT " <file:<n>>",    \
         "use given file name and line number as entry point")                 \
    << help_entry(                                                             \
         "--" MEMORY_SNAPSHOT_HARNESS_HAVOC_VARIABLES_OPT " vars",             \
         "initialize variables from `vars' to non-deterministic values")       \
    << COMMON_HARNESS_GENERATOR_HELP                                           \
    << help_entry(                                                             \
         "--" MEMORY_SNAPSHOT_HARNESS_TREAT_POINTER_AS_ARRAY_OPT " p",         \
         "treat the global pointer with the name `p' as an array")             \
    << help_entry(                                                             \
         "--" MEMORY_SNAPSHOT_HARNESS_ASSOCIATED_ARRAY_SIZE_OPT                \
         " array_name:size_name",                                              \
         "set the parameter <size_name> to the size of the array "             \
         "<array_name> (implies "                                              \
         "-- " MEMORY_SNAPSHOT_HARNESS_TREAT_POINTER_AS_ARRAY_OPT              \
         " <array_name>)")

#endif // CPROVER_GOTO_HARNESS_MEMORY_SNAPSHOT_HARNESS_GENERATOR_OPTIONS_H
