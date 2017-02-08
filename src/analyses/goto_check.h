/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

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
  const namespacet &ns,
  const optionst &options,
  goto_functionst::goto_functiont &goto_function);

void goto_check(
  const optionst &options,
  goto_modelt &goto_model);

#define OPT_GOTO_CHECK \
  "(bounds-check)(pointer-check)(memory-leak-check)" \
  "(div-by-zero-check)(signed-overflow-check)(unsigned-overflow-check)" \
  "(pointer-overflow-check)(conversion-check)(undefined-shift-check)" \
  "(float-overflow-check)(nan-check)"

#define HELP_GOTO_CHECK \
  " --bounds-check               enable array bounds checks\n" \
  " --pointer-check              enable pointer checks\n" \
  " --memory-leak-check          enable memory leak checks\n" \
  " --div-by-zero-check          enable division by zero checks\n" \
  " --signed-overflow-check      enable signed arithmetic over- and underflow checks\n" \
  " --unsigned-overflow-check    enable arithmetic over- and underflow checks\n" \
  " --pointer-overflow-check     enable pointer arithmetic over- and underflow checks\n" \
  " --conversion-check           check whether values can be represented after type cast\n" \
  " --undefined-shift-check      check shift greater than bit-width\n" \
  " --float-overflow-check       check floating-point for +/-Inf\n" \
  " --nan-check                  check floating-point for NaN\n" \

#define PARSE_OPTIONS_GOTO_CHECK(cmdline, options) \
  options.set_option("bounds-check", cmdline.isset("bounds-check")); \
  options.set_option("pointer-check", cmdline.isset("pointer-check")); \
  options.set_option("memory-leak-check", cmdline.isset("memory-leak-check")); \
  options.set_option("div-by-zero-check", cmdline.isset("div-by-zero-check")); \
  options.set_option("signed-overflow-check", cmdline.isset("signed-overflow-check")); \
  options.set_option("unsigned-overflow-check", cmdline.isset("unsigned-overflow-check")); \
  options.set_option("pointer-overflow-check", cmdline.isset("pointer-overflow-check")); \
  options.set_option("conversion-check", cmdline.isset("conversion-check")); \
  options.set_option("undefined-shift-check", cmdline.isset("undefined-shift-check")); \
  options.set_option("float-overflow-check", cmdline.isset("float-overflow-check")); \
  options.set_option("nan-check", cmdline.isset("nan-check"))

#endif // CPROVER_ANALYSES_GOTO_CHECK_H
