/******************************************************************\

Module: functions_harness_generator_options

Author: Diffblue Ltd.

\******************************************************************/

#ifndef CPROVER_GOTO_HARNESS_FUNCTION_HARNESS_GENERATOR_OPTIONS_H
#define CPROVER_GOTO_HARNESS_FUNCTION_HARNESS_GENERATOR_OPTIONS_H

#define FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT "function"

// clang-format off
#define FUNCTION_HARNESS_GENERATOR_OPTIONS                                     \
  "(" FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT "):"                             \

// clang-format on

// clang-format off
#define FUNCTION_HARNESS_GENERATOR_HELP                                        \
  "function harness generator (--harness-type call-function)\n\n"              \
  "--" FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT                                 \
  "      the function the harness should call\n"                               \
  // FUNCTION_HARNESS_GENERATOR_HELP

// clang-format on

#endif // CPROVER_GOTO_HARNESS_FUNCTION_HARNESS_GENERATOR_OPTIONS_H
