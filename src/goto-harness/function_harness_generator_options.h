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
#define FUNCTION_HARNESS_GENERATOR_TREAT_POINTERS_EQUAL_OPT                    \
  "treat-pointers-equal"
#define FUNCTION_HARNESS_GENERATOR_ASSOCIATED_ARRAY_SIZE_OPT                   \
  "associated-array-size"
#define FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_CSTRING                    \
  "treat-pointer-as-cstring"
#define FUNCTION_HARNESS_GENERATOR_TREAT_POINTERS_EQUAL_MAYBE_OPT              \
  "treat-pointers-equal-maybe"

#define FUNCTION_HARNESS_GENERATOR_OPTIONS                                     \
  "(" FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT                                  \
  "):"                                                                         \
  "(" FUNCTION_HARNESS_GENERATOR_NONDET_GLOBALS_OPT                            \
  ")"                                                                          \
  "(" FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_ARRAY_OPT                    \
  "):"                                                                         \
  "(" FUNCTION_HARNESS_GENERATOR_TREAT_POINTERS_EQUAL_OPT                      \
  "):"                                                                         \
  "(" FUNCTION_HARNESS_GENERATOR_ASSOCIATED_ARRAY_SIZE_OPT                     \
  "):"                                                                         \
  "(" FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_CSTRING                      \
  "):"                                                                         \
  "(" FUNCTION_HARNESS_GENERATOR_TREAT_POINTERS_EQUAL_MAYBE_OPT ")"

#define FUNCTION_HARNESS_GENERATOR_HELP                                        \
  "function harness generator (--harness-type call-function):\n"               \
    << help_entry(                                                             \
         "--" FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT " <function-name>",      \
         "the function the harness should call")                               \
    << help_entry(                                                             \
         "--" FUNCTION_HARNESS_GENERATOR_NONDET_GLOBALS_OPT,                   \
         "set global variables to non-deterministic values in harness")        \
    << COMMON_HARNESS_GENERATOR_HELP                                           \
    << help_entry(                                                             \
         "--" FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_ARRAY_OPT " p",      \
         "treat the function parameter with the name `p' as an array")         \
    << help_entry(                                                             \
         "--" FUNCTION_HARNESS_GENERATOR_TREAT_POINTERS_EQUAL_OPT              \
         " p,q,r[;s,t]",                                                       \
         "treat the function parameters `q,r' equal to parameter `p'; `s` to " \
         "`t` and so on")                                                      \
    << help_entry(                                                             \
         "--" FUNCTION_HARNESS_GENERATOR_TREAT_POINTERS_EQUAL_MAYBE_OPT,       \
         "function parameters equality is non-deterministic")                  \
    << help_entry(                                                             \
         "--" FUNCTION_HARNESS_GENERATOR_ASSOCIATED_ARRAY_SIZE_OPT             \
         " array_name:size_name",                                              \
         "set the parameter <size_name> to the size of the array "             \
         "<array_name> (implies "                                              \
         "-- " FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_ARRAY_OPT           \
         " <array_name>)")                                                     \
    << help_entry(                                                             \
         "--" FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_CSTRING " p",        \
         "treat the function parameter with the name `p' as a string of "      \
         "characters")

#endif // CPROVER_GOTO_HARNESS_FUNCTION_HARNESS_GENERATOR_OPTIONS_H
