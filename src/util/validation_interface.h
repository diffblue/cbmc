/*******************************************************************\

Module: Goto program validation common command line options

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_UTIL_VALIDATION_INTERFACE_H
#define CPROVER_UTIL_VALIDATION_INTERFACE_H

#define OPT_VALIDATE                                                           \
  "(validate-goto-model)"                                                      \
  "(validate-ssa-equation)"

#define HELP_VALIDATE                                                          \
  " {y--validate-goto-model} \t "                                              \
  "enable additional well-formedness checks on the goto program\n"             \
  " {y--validate-ssa-equation} \t "                                            \
  "enable additional well-formedness checks on the SSA representation\n"

#endif /* CPROVER_UTIL_VALIDATION_INTERFACE_H */
