/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#ifndef CPROVER_ANALYSES_GOTO_CHECK_H
#define CPROVER_ANALYSES_GOTO_CHECK_H

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_model.h>

class namespacet;
class optionst;

void goto_check(
  const namespacet &ns,
  const optionst &options,
  goto_functionst &goto_functions);

void goto_check(
  const irep_idt &function_identifier,
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  const optionst &options);

void goto_check(
  const optionst &options,
  goto_modelt &goto_model);

#define OPT_GOTO_CHECK                                                         \
  "(bounds-check)(pointer-check)(memory-leak-check)"                           \
  "(div-by-zero-check)(enum-range-check)(signed-overflow-check)(unsigned-"     \
  "overflow-check)"                                                            \
  "(pointer-overflow-check)(conversion-check)(undefined-shift-check)"          \
  "(float-overflow-check)(nan-check)(no-built-in-assertions)"                  \
  "(pointer-primitive-check)"                                                  \
  "(overly-large-allocation-check)"

// clang-format off
#define HELP_GOTO_CHECK \
  " --bounds-check               enable array bounds checks\n" \
  " --pointer-check              enable pointer checks\n" /* NOLINT(whitespace/line_length) */ \
  " --memory-leak-check          enable memory leak checks\n" \
  " --div-by-zero-check          enable division by zero checks\n" \
  " --signed-overflow-check      enable signed arithmetic over- and underflow checks\n" /* NOLINT(whitespace/line_length) */ \
  " --unsigned-overflow-check    enable arithmetic over- and underflow checks\n" /* NOLINT(whitespace/line_length) */  \
  " --pointer-overflow-check     enable pointer arithmetic over- and underflow checks\n" /* NOLINT(whitespace/line_length) */  \
  " --conversion-check           check whether values can be represented after type cast\n" /* NOLINT(whitespace/line_length) */  \
  " --undefined-shift-check      check shift greater than bit-width\n" \
  " --float-overflow-check       check floating-point for +/-Inf\n" \
  " --nan-check                  check floating-point for NaN\n" \
  " --no-built-in-assertions     ignore assertions in built-in library\n" \
  " --enum-range-check           checks that all enum type expressions have values in the enum range\n" /* NOLINT(whitespace/line_length) */ \
  " --pointer-primitive-check    checks that all pointers in pointer primitives are valid or null\n" /* NOLINT(whitespace/line_length) */ \
  << help_entry( \
    "--overly-large-allocation-check", \
    "checks that no individual allocation exceeds CBMC's address space limit")

#define PARSE_OPTIONS_GOTO_CHECK(cmdline, options) \
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
  options.set_option("overly-large-allocation-check", cmdline.isset("overly-large-allocation-check")) /* NOLINT(whitespace/line_length) */
// clang-format on

#endif // CPROVER_ANALYSES_GOTO_CHECK_H
