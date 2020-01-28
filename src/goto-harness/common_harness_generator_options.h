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

// clang-format off
#define COMMON_HARNESS_GENERATOR_OPTIONS                                       \
  "(" COMMON_HARNESS_GENERATOR_MIN_NULL_TREE_DEPTH_OPT "):"                    \
  "(" COMMON_HARNESS_GENERATOR_MAX_NONDET_TREE_DEPTH_OPT "):"                  \
  "(" COMMON_HARNESS_GENERATOR_MIN_ARRAY_SIZE_OPT "):"                         \
  "(" COMMON_HARNESS_GENERATOR_MAX_ARRAY_SIZE_OPT "):"                         \
  "(" COMMON_HARNESS_GENERATOR_FUNCTION_POINTER_CAN_BE_NULL_OPT "):"           \
  "(" COMMON_HARNESS_GENERATOR_HAVOC_MEMBER_OPT "):"                           \
// COMMON_HARNESS_GENERATOR_OPTIONS

// clang-format on

// clang-format off
#define COMMON_HARNESS_GENERATOR_HELP                                          \
  "--" COMMON_HARNESS_GENERATOR_MIN_NULL_TREE_DEPTH_OPT                        \
  " N       minimum level at which a pointer can first be NULL\n"              \
  "                              in a recursively nondet initialized struct\n" \
  "--" COMMON_HARNESS_GENERATOR_MAX_NONDET_TREE_DEPTH_OPT                      \
  " N     limit size of nondet (e.g. input) object tree;\n"                    \
  "                              at level N pointers are set to null\n"        \
  "--" COMMON_HARNESS_GENERATOR_MIN_ARRAY_SIZE_OPT                             \
  " N            minimum size of dynamically created arrays\n"                 \
  "                              (default: 1)\n"                               \
  "--" COMMON_HARNESS_GENERATOR_MAX_ARRAY_SIZE_OPT                             \
  " N            maximum size of dynamically created arrays\n"                 \
  "                              (default: 2)\n"                               \
  "--" COMMON_HARNESS_GENERATOR_FUNCTION_POINTER_CAN_BE_NULL_OPT               \
  " <function-name>,  name of the function(s) pointer parameters\n"            \
  "              that can be NULL pointing."                                   \
  "--" COMMON_HARNESS_GENERATOR_HAVOC_MEMBER_OPT                               \
  "              path to the member to be havoced\n"                           \
  // COMMON_HARNESS_GENERATOR_HELP

// clang-format on

#endif // CPROVER_GOTO_HARNESS_COMMON_HARNESS_GENERATOR_OPTIONS_H
