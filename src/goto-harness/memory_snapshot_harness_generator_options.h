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
  "memory snapshot harness generator ({y--harness-type}\n"                     \
  "  {yinitialize-with-memory-snapshot}):\n"                                   \
  " {y--" MEMORY_SNAPSHOT_HARNESS_SNAPSHOT_OPT                                 \
  "} {ufile} \t "                                                              \
  "initialize memory from JSON memory snapshot\n"                              \
  " {y--" MEMORY_SNAPSHOT_HARNESS_INITIAL_GOTO_LOC_OPT                         \
  "} {ufunc}[{y:}{un}] "                                                       \
  "\t "                                                                        \
  "use given function and location number as entry point\n"                    \
  " {y--" MEMORY_SNAPSHOT_HARNESS_INITIAL_SOURCE_LOC_OPT                       \
  "} {ufile}{y:}{un} "                                                         \
  "\t "                                                                        \
  "use given file name and line number as entry point\n"                       \
  " {y--" MEMORY_SNAPSHOT_HARNESS_HAVOC_VARIABLES_OPT                          \
  "} {uvars} \t "                                                              \
  "initialize variables from {uvars} to non-deterministic "                    \
  "values\n" COMMON_HARNESS_GENERATOR_HELP                                     \
  " {y--" MEMORY_SNAPSHOT_HARNESS_TREAT_POINTER_AS_ARRAY_OPT                   \
  "} {up} \t "                                                                 \
  "treat the global pointer with the name {up} as an array\n"                  \
  " {y--" MEMORY_SNAPSHOT_HARNESS_ASSOCIATED_ARRAY_SIZE_OPT                    \
  "} "                                                                         \
  "{uarray_name}{y:}{usize_name} \t "                                          \
  "set the parameter {usize_name} to the size of the array {uarray_name} "     \
  "(implies "                                                                  \
  "{y-- " MEMORY_SNAPSHOT_HARNESS_TREAT_POINTER_AS_ARRAY_OPT                   \
  "} "                                                                         \
  "{uarray_name})\n"

#endif // CPROVER_GOTO_HARNESS_MEMORY_SNAPSHOT_HARNESS_GENERATOR_OPTIONS_H
