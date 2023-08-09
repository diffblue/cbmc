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
  "function harness generator ({y--harness-type} {ycall-function}):\n"         \
  " {y--" FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT                              \
  "} {ufunction_name} \t "                                                     \
  "the function the harness should call\n"                                     \
  " {y--" FUNCTION_HARNESS_GENERATOR_NONDET_GLOBALS_OPT                        \
  "} \t "                                                                      \
  "set global variables to non-deterministic values in "                       \
  "harness\n" COMMON_HARNESS_GENERATOR_HELP                                    \
  " {y--" FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_ARRAY_OPT                \
  "} {up} \t "                                                                 \
  "treat the function parameter with the name {up} as an array\n"              \
  " {y--" FUNCTION_HARNESS_GENERATOR_TREAT_POINTERS_EQUAL_OPT                  \
  "} "                                                                         \
  "{up}{y,}{uq}{y,}{ur}[{y;}{us}{y,}{ut}] \t "                                 \
  "treat the function parameters {uq}{y,}{ur} equal to parameter {up}; "       \
  "{us} to {ut} and so on\n"                                                   \
  " {y--" FUNCTION_HARNESS_GENERATOR_TREAT_POINTERS_EQUAL_MAYBE_OPT            \
  "} \t "                                                                      \
  "function parameters equality is non-deterministic\n"                        \
  " {y--" FUNCTION_HARNESS_GENERATOR_ASSOCIATED_ARRAY_SIZE_OPT                 \
  "} "                                                                         \
  "{uarray_name}{y:}{usize_name} \t "                                          \
  "set the parameter {usize_name} to the size of the array {uarray_name} "     \
  "(implies "                                                                  \
  "{y-- " FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_ARRAY_OPT                \
  "} "                                                                         \
  "{uarray_name})\n"                                                           \
  " {y--" FUNCTION_HARNESS_GENERATOR_TREAT_POINTER_AS_CSTRING                  \
  "} {up} \t "                                                                 \
  "treat the function parameter with the name {up} as a string of "            \
  "characters\n"

#endif // CPROVER_GOTO_HARNESS_FUNCTION_HARNESS_GENERATOR_OPTIONS_H
