/******************************************************************\

Module: functions_harness_generator_options

Author: Diffblue Ltd.

\******************************************************************/

#ifndef CPROVER_GOTO_HARNESS_FUNCTION_HARNESS_GENERATOR_OPTIONS_H
#define CPROVER_GOTO_HARNESS_FUNCTION_HARNESS_GENERATOR_OPTIONS_H

#include "common_harness_generator_options.h"

#define FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT "function"
#define FUNCTION_HARNESS_GENERATOR_NONDET_GLOBALS_OPT "nondet-globals"
#define FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_ARRAY_OPT                  \
  "treat-pointer-as-array"
#define FUNCTION_HARNESS_GENERATOR_ASSOCIATED_ARRAY_SIZE_OPT                   \
  "associated-array-size"
#define FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_CSTRING                    \
  "treat-pointer-as-cstring"

// clang-format off
#define FUNCTION_HARNESS_GENERATOR_OPTIONS                                     \
  "(" FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT "):"                             \
  "(" FUNCTION_HARNESS_GENERATOR_NONDET_GLOBALS_OPT ")"                        \
  "(" FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_ARRAY_OPT "):"               \
  "(" FUNCTION_HARNESS_GENERATOR_ASSOCIATED_ARRAY_SIZE_OPT "):"                \
  "(" FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_CSTRING "):"                 \
// FUNCTION_HARNESS_GENERATOR_OPTIONS

// clang-format on

// clang-format off
#define FUNCTION_HARNESS_GENERATOR_HELP                                        \
  "function harness generator (--harness-type call-function)\n\n"              \
  "--" FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT                                 \
  "                    the function the harness should call\n"                 \
  "--" FUNCTION_HARNESS_GENERATOR_NONDET_GLOBALS_OPT                           \
  "              set global variables to non-deterministic values\n"           \
  "                              in harness\n"                                 \
  COMMON_HARNESS_GENERATOR_HELP                                                \
  "--" FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_ARRAY_OPT                   \
  " p    treat the function parameter with the name `p' as\n"                  \
  "                              an array\n"                                   \
  "--" FUNCTION_HARNESS_GENERATOR_ASSOCIATED_ARRAY_SIZE_OPT                    \
  " array_name:size_name\n"                                                    \
  "                              set the parameter <size_name> to the size"    \
  " of\n                              the array <array_name>\n"                \
  "                              (implies "                                    \
  "-- " FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_ARRAY_OPT                  \
  " <array_name>)\n"                                                           \
  "--" FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_CSTRING                     \
  " p    treat the function parameter with the name `p' as\n"                  \
  "                              a string of characters\n"                     \
  // FUNCTION_HARNESS_GENERATOR_HELP

// clang-format on

#endif // CPROVER_GOTO_HARNESS_FUNCTION_HARNESS_GENERATOR_OPTIONS_H
