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

// clang-format off
#define MEMORY_SNAPSHOT_HARNESS_GENERATOR_OPTIONS                              \
  "(" MEMORY_SNAPSHOT_HARNESS_SNAPSHOT_OPT "):"                                \
  "(" MEMORY_SNAPSHOT_HARNESS_INITIAL_GOTO_LOC_OPT "):"                        \
  "(" MEMORY_SNAPSHOT_HARNESS_INITIAL_SOURCE_LOC_OPT "):"                      \
  "(" MEMORY_SNAPSHOT_HARNESS_HAVOC_VARIABLES_OPT "):"                         \
  "(" MEMORY_SNAPSHOT_HARNESS_TREAT_POINTER_AS_ARRAY_OPT "):"                  \
  "(" MEMORY_SNAPSHOT_HARNESS_ASSOCIATED_ARRAY_SIZE_OPT "):"                   \
// MEMORY_SNAPSHOT_HARNESS_GENERATOR_OPTIONS

// clang-format on

// clang-format off
#define MEMORY_SNAPSHOT_HARNESS_GENERATOR_HELP                                 \
  "memory snapshot harness generator (--harness-type\n"                        \
  "  initialise-from-memory-snapshot)\n\n"                                     \
  "--" MEMORY_SNAPSHOT_HARNESS_SNAPSHOT_OPT " <file>      initialise memory "  \
  "from JSON memory snapshot\n"                                                \
  "--" MEMORY_SNAPSHOT_HARNESS_INITIAL_GOTO_LOC_OPT " <func[:<n>]>\n"          \
  "                              use given function and location number as "   \
  "entry\n                              point\n"                               \
  "--" MEMORY_SNAPSHOT_HARNESS_INITIAL_SOURCE_LOC_OPT " <file:<n>>\n"          \
  "                              use given file name and line number as "      \
  "entry\n                              point\n"                               \
  "--" MEMORY_SNAPSHOT_HARNESS_HAVOC_VARIABLES_OPT " vars        initialise"   \
  " variables from `vars' to\n"                                                \
  "                              non-deterministic values\n"                   \
  COMMON_HARNESS_GENERATOR_HELP                                                \
  "--" MEMORY_SNAPSHOT_HARNESS_TREAT_POINTER_AS_ARRAY_OPT                      \
  " p    treat the global pointer with the name `p' as\n"                      \
  "                              an array\n"                                   \
  "--" MEMORY_SNAPSHOT_HARNESS_ASSOCIATED_ARRAY_SIZE_OPT                       \
  " array_name:size_name\n"                                                    \
  "                              set the parameter <size_name> to the size"    \
  " of\n                              the array <array_name>\n"                \
  "                              (implies "                                    \
  "-- " MEMORY_SNAPSHOT_HARNESS_TREAT_POINTER_AS_ARRAY_OPT                     \
  " <array_name>)\n"                                                           \
// MEMORY_SNAPSHOT_HARNESS_GENERATOR_HELP

// clang-format on

#endif // CPROVER_GOTO_HARNESS_MEMORY_SNAPSHOT_HARNESS_GENERATOR_OPTIONS_H
