/*******************************************************************\

Module: Checks for Errors in Java Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Check for Errors in Java Programs

#ifndef CPROVER_ANALYSES_GOTO_CHECK_JAVA_H
#define CPROVER_ANALYSES_GOTO_CHECK_JAVA_H

#include <goto-programs/goto_functions.h>

class goto_modelt;
class namespacet;
class optionst;
class message_handlert;

void goto_check_java(
  const namespacet &ns,
  const optionst &options,
  goto_functionst &goto_functions,
  message_handlert &message_handler);

void goto_check_java(
  const irep_idt &function_identifier,
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  const optionst &options,
  message_handlert &message_handler);

void goto_check_java(
  const optionst &options,
  goto_modelt &goto_model,
  message_handlert &message_handler);

#define OPT_GOTO_CHECK_JAVA                                                    \
  "(bounds-check)(pointer-check)"                                              \
  "(div-by-zero-check)(enum-range-check)(signed-overflow-check)(unsigned-"     \
  "overflow-check)"                                                            \
  "(conversion-check)"                                                         \
  "(float-overflow-check)(nan-check)(no-built-in-assertions)"                  \
  "(retain-trivial-checks)"                                                    \
  "(error-label):"                                                             \
  "(no-assertions)(no-assumptions)"                                            \
  "(assert-to-assume)"

// clang-format off
#define HELP_GOTO_CHECK_JAVA \
  " --bounds-check               enable array bounds checks\n" \
  " --pointer-check              enable pointer checks\n" /* NOLINT(whitespace/line_length) */ \
  " --div-by-zero-check          enable division by zero checks\n" \
  " --signed-overflow-check      enable signed arithmetic over- and underflow checks\n" /* NOLINT(whitespace/line_length) */ \
  " --unsigned-overflow-check    enable arithmetic over- and underflow checks\n" /* NOLINT(whitespace/line_length) */  \
  " --conversion-check           check whether values can be represented after type cast\n" /* NOLINT(whitespace/line_length) */  \
  " --float-overflow-check       check floating-point for +/-Inf\n" \
  " --nan-check                  check floating-point for NaN\n" \
  " --retain-trivial-checks      include checks that are trivially true\n" \
  " --error-label label          check that label is unreachable\n" \
  " --no-built-in-assertions     ignore assertions in built-in library\n" \
  " --no-assertions              ignore user assertions\n" \
  " --no-assumptions             ignore user assumptions\n" \
  " --assert-to-assume           convert user assertions to assumptions\n" \

#define PARSE_OPTIONS_GOTO_CHECK_JAVA(cmdline, options) \
  options.set_option("bounds-check", cmdline.isset("bounds-check")); \
  options.set_option("pointer-check", cmdline.isset("pointer-check")); \
  options.set_option("memory-leak-check", cmdline.isset("memory-leak-check")); \
  options.set_option("div-by-zero-check", cmdline.isset("div-by-zero-check")); \
  options.set_option("enum-range-check", cmdline.isset("enum-range-check")); \
  options.set_option("signed-overflow-check", cmdline.isset("signed-overflow-check")); /* NOLINT(whitespace/line_length) */  \
  options.set_option("unsigned-overflow-check", cmdline.isset("unsigned-overflow-check")); /* NOLINT(whitespace/line_length) */  \
  options.set_option("pointer-overflow-check", cmdline.isset("pointer-overflow-check")); /* NOLINT(whitespace/line_length) */  \
  options.set_option("conversion-check", cmdline.isset("conversion-check")); \
  options.set_option("undefined-shift-check", cmdline.isset("undefined-shift-check")); /* NOLINT(whitespace/line_length) */  \
  options.set_option("float-overflow-check", cmdline.isset("float-overflow-check")); /* NOLINT(whitespace/line_length) */  \
  options.set_option("nan-check", cmdline.isset("nan-check")); \
  options.set_option("built-in-assertions", !cmdline.isset("no-built-in-assertions")); /* NOLINT(whitespace/line_length) */ \
  options.set_option("pointer-primitive-check", cmdline.isset("pointer-primitive-check")); /* NOLINT(whitespace/line_length) */ \
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

#endif // CPROVER_ANALYSES_GOTO_CHECK_JAVA_H
