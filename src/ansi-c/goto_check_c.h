/*******************************************************************\

Module: Checks for Errors in C/C++ Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#ifndef CPROVER_ANSI_C_GOTO_CHECK_C_H
#define CPROVER_ANSI_C_GOTO_CHECK_C_H

#include <goto-programs/goto_functions.h>

class goto_modelt;
class namespacet;
class optionst;
class message_handlert;

void goto_check_c(
  const namespacet &ns,
  const optionst &options,
  goto_functionst &goto_functions,
  message_handlert &message_handler);

void goto_check_c(
  const irep_idt &function_identifier,
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  const optionst &options,
  message_handlert &message_handler);

void goto_check_c(
  const optionst &options,
  goto_modelt &goto_model,
  message_handlert &message_handler);

#define OPT_GOTO_CHECK                                                         \
  "(bounds-check)(pointer-check)(memory-leak-check)(memory-cleanup-check)"     \
  "(div-by-zero-check)(enum-range-check)"                                      \
  "(signed-overflow-check)(unsigned-overflow-check)"                           \
  "(pointer-overflow-check)(conversion-check)(undefined-shift-check)"          \
  "(float-overflow-check)(nan-check)(no-built-in-assertions)"                  \
  "(pointer-primitive-check)"                                                  \
  "(retain-trivial-checks)"                                                    \
  "(error-label):"                                                             \
  "(no-assertions)(no-assumptions)"                                            \
  "(assert-to-assume)"

#define HELP_GOTO_CHECK                                                        \
  " {y--bounds-check} \t enable array bounds checks\n"                         \
  " {y--pointer-check} \t enable pointer checks\n"                             \
  " {y--memory-leak-check} \t enable memory leak checks\n"                     \
  " {y--memory-cleanup-check} \t enable memory cleanup checks\n"               \
  " {y--div-by-zero-check} \t enable division by zero checks\n"                \
  " {y--signed-overflow-check} \t "                                            \
  "enable signed arithmetic over- and underflow checks\n"                      \
  " {y--unsigned-overflow-check} \t "                                          \
  "enable arithmetic over- and underflow checks\n"                             \
  " {y--pointer-overflow-check} \t "                                           \
  "enable pointer arithmetic over- and underflow checks\n"                     \
  " {y--conversion-check} \t "                                                 \
  "check whether values can be represented after type cast\n"                  \
  " {y--undefined-shift-check} \t check shift greater than bit-width\n"        \
  " {y--float-overflow-check} \t check floating-point for +/-Inf\n"            \
  " {y--nan-check} \t check floating-point for NaN\n"                          \
  " {y--enum-range-check} \t "                                                 \
  "checks that all enum type expressions have values in the enum range\n"      \
  " {y--pointer-primitive-check} \t "                                          \
  "checks that all pointers in pointer primitives are valid or null\n"         \
  " {y--retain-trivial-checks} \t include checks that are trivially true\n"    \
  " {y--error-label} {ulabel} \t check that label {ulabel} is unreachable\n"   \
  " {y--no-built-in-assertions} \t ignore assertions in built-in library\n"    \
  " {y--no-assertions} \t ignore user assertions\n"                            \
  " {y--no-assumptions} \t ignore user assumptions\n"                          \
  " {y--assert-to-assume} \t convert user assertions to assumptions\n"

// clang-format off
#define PARSE_OPTIONS_GOTO_CHECK(cmdline, options) \
  options.set_option("bounds-check", !cmdline.isset("no-bounds-check")); \
  options.set_option("pointer-check", !cmdline.isset("no-pointer-check")); \
  options.set_option("memory-leak-check", cmdline.isset("memory-leak-check")); \
  options.set_option("memory-cleanup-check", cmdline.isset("memory-cleanup-check")); /* NOLINT(whitespace/line_length) */ \
  options.set_option("div-by-zero-check", !cmdline.isset("no-div-by-zero-check")); \
  options.set_option("enum-range-check", cmdline.isset("enum-range-check")); \
  options.set_option("signed-overflow-check", !cmdline.isset("no-signed-overflow-check")); /* NOLINT(whitespace/line_length) */  \
  options.set_option("unsigned-overflow-check", cmdline.isset("unsigned-overflow-check")); /* NOLINT(whitespace/line_length) */  \
  options.set_option("pointer-overflow-check", cmdline.isset("pointer-overflow-check")); /* NOLINT(whitespace/line_length) */  \
  options.set_option("conversion-check", cmdline.isset("conversion-check")); \
  options.set_option("undefined-shift-check", !cmdline.isset("no-undefined-shift-check")); /* NOLINT(whitespace/line_length) */  \
  options.set_option("float-overflow-check", cmdline.isset("float-overflow-check")); /* NOLINT(whitespace/line_length) */  \
  options.set_option("nan-check", cmdline.isset("nan-check")); \
  options.set_option("built-in-assertions", !cmdline.isset("no-built-in-assertions")); /* NOLINT(whitespace/line_length) */ \
  options.set_option("pointer-primitive-check", !cmdline.isset("no-pointer-primitive-check")); /* NOLINT(whitespace/line_length) */ \
  options.set_option("retain-trivial-checks", \
                     cmdline.isset("retain-trivial-checks")); \
  options.set_option("assertions", !cmdline.isset("no-assertions")); /* NOLINT(whitespace/line_length) */ \
  options.set_option("assumptions", !cmdline.isset("no-assumptions")); /* NOLINT(whitespace/line_length) */ \
  options.set_option("assert-to-assume", cmdline.isset("assert-to-assume")); /* NOLINT(whitespace/line_length) */ \
  options.set_option("retain-trivial", cmdline.isset("retain-trivial")); /* NOLINT(whitespace/line_length) */ \
  if(cmdline.isset("error-label")) \
    options.set_option("error-label", cmdline.get_values("error-label")); \
  (void)0
// clang-format on

#endif // CPROVER_ANALYSES_GOTO_CHECK_C_H
