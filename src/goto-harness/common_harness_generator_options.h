/******************************************************************\

Module: common_harness_generator_options

Author: Diffblue Ltd.

\******************************************************************/

#ifndef CPROVER_GOTO_HARNESS_COMMON_HARNESS_GENERATOR_OPTIONS_H
#define CPROVER_GOTO_HARNESS_COMMON_HARNESS_GENERATOR_OPTIONS_H

#define COMMON_HARNESS_GENERATOR_MIN_NULL_TREE_DEPTH_OPT "min-null-tree-depth"
#define COMMON_HARNESS_GENERATOR_MAX_NONDET_TREE_DEPTH_OPT                     \
  "max-nondet-tree-depth"
#define COMMON_HARNESS_GENERATOR_MIN_ARRAY_SIZE_OPT "min-array-size"
#define COMMON_HARNESS_GENERATOR_MAX_ARRAY_SIZE_OPT "max-array-size"
#define COMMON_HARNESS_GENERATOR_FUNCTION_POINTER_CAN_BE_NULL_OPT              \
  "function-pointer-can-be-null"
#define COMMON_HARNESS_GENERATOR_HAVOC_MEMBER_OPT "havoc-member"

#define COMMON_HARNESS_GENERATOR_OPTIONS                                       \
  "(" COMMON_HARNESS_GENERATOR_MIN_NULL_TREE_DEPTH_OPT                         \
  "):"                                                                         \
  "(" COMMON_HARNESS_GENERATOR_MAX_NONDET_TREE_DEPTH_OPT                       \
  "):"                                                                         \
  "(" COMMON_HARNESS_GENERATOR_MIN_ARRAY_SIZE_OPT                              \
  "):"                                                                         \
  "(" COMMON_HARNESS_GENERATOR_MAX_ARRAY_SIZE_OPT                              \
  "):"                                                                         \
  "(" COMMON_HARNESS_GENERATOR_FUNCTION_POINTER_CAN_BE_NULL_OPT                \
  "):"                                                                         \
  "(" COMMON_HARNESS_GENERATOR_HAVOC_MEMBER_OPT "):"

#define COMMON_HARNESS_GENERATOR_HELP                                          \
  " {y--" COMMON_HARNESS_GENERATOR_MIN_NULL_TREE_DEPTH_OPT                     \
  "} {uN} \t "                                                                 \
  "minimum level at which a pointer can first be NULL in a recursively "       \
  "nondet initialized struct\n"                                                \
  " {y--" COMMON_HARNESS_GENERATOR_MAX_NONDET_TREE_DEPTH_OPT                   \
  "} {uN} \t "                                                                 \
  "limit size of nondet (e.g. input) object tree; at level {uN} pointers "     \
  "are set to null\n"                                                          \
  " {y--" COMMON_HARNESS_GENERATOR_MIN_ARRAY_SIZE_OPT                          \
  "} {uN} \t "                                                                 \
  "minimum size of dynamically created arrays (default: 1)\n"                  \
  " {y--" COMMON_HARNESS_GENERATOR_MAX_ARRAY_SIZE_OPT                          \
  "} {uN} \t "                                                                 \
  "maximum size of dynamically created arrays (default: 2)\n"                  \
  " {y--" COMMON_HARNESS_GENERATOR_FUNCTION_POINTER_CAN_BE_NULL_OPT            \
  "} "                                                                         \
  "{ufunction_name} \t "                                                       \
  "name of the function(s) pointer parameters that can be NULL "               \
  "pointing\n"                                                                 \
  " {y--" COMMON_HARNESS_GENERATOR_HAVOC_MEMBER_OPT                            \
  "} {umember_expr} \t "                                                       \
  "path to the member to be havocked\n"

#endif // CPROVER_GOTO_HARNESS_COMMON_HARNESS_GENERATOR_OPTIONS_H
