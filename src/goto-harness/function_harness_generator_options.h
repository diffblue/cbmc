/******************************************************************\

Module: functions_harness_generator_options

Author: Diffblue Ltd.

\******************************************************************/

#ifndef CPROVER_GOTO_HARNESS_FUNCTION_HARNESS_GENERATOR_OPTIONS_H
#define CPROVER_GOTO_HARNESS_FUNCTION_HARNESS_GENERATOR_OPTIONS_H

#define FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT "function"
#define FUNCTION_HARNESS_GENERATOR_NONDET_GLOBALS_OPT "nondet-globals"
#define FUNCTION_HARNESS_GENERATOR_MIN_NULL_TREE_DEPTH_OPT "min-null-tree-depth"
#define FUNCTION_HARNESS_GENERATOR_MAX_NONDET_TREE_DEPTH_OPT                   \
  "max-nondet-tree-depth"

// clang-format off
#define FUNCTION_HARNESS_GENERATOR_OPTIONS                                     \
  "(" FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT "):"                             \
  "(" FUNCTION_HARNESS_GENERATOR_NONDET_GLOBALS_OPT ")"                        \
  "(" FUNCTION_HARNESS_GENERATOR_MIN_NULL_TREE_DEPTH_OPT "):"                  \
  "(" FUNCTION_HARNESS_GENERATOR_MAX_NONDET_TREE_DEPTH_OPT "):"                \
// FUNCTION_HARNESS_GENERATOR_OPTIONS

// clang-format on

// clang-format off
#define FUNCTION_HARNESS_GENERATOR_HELP                                        \
  "function harness generator (--harness-type call-function)\n\n"              \
  "--" FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT                                 \
  "      the function the harness should call\n"                               \
  "--" FUNCTION_HARNESS_GENERATOR_NONDET_GLOBALS_OPT                           \
  "      set global variables to non-deterministic values in harness\n"        \
  "--" FUNCTION_HARNESS_GENERATOR_MIN_NULL_TREE_DEPTH_OPT                      \
  " N      minimum level at which a pointer can first be\n"                    \
  "        NULL in a recursively nondet initialized struct\n"                  \
  "--" FUNCTION_HARNESS_GENERATOR_MAX_NONDET_TREE_DEPTH_OPT                    \
  " N    limit size of nondet (e.g. input) object tree;\n"                     \
  "      at level N pointers are set to null\n"                                \
  // FUNCTION_HARNESS_GENERATOR_HELP

// clang-format on

#endif // CPROVER_GOTO_HARNESS_FUNCTION_HARNESS_GENERATOR_OPTIONS_H
