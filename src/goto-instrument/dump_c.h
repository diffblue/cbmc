/*******************************************************************\

Module: Dump C from Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Dump C from Goto Program

#ifndef CPROVER_GOTO_INSTRUMENT_DUMP_C_H
#define CPROVER_GOTO_INSTRUMENT_DUMP_C_H

#include <iosfwd>
#include <string>

class goto_functionst;
class namespacet;

void dump_c(
  const goto_functionst &src,
  const bool use_system_headers,
  const bool use_all_headers,
  const bool include_harness,
  const namespacet &ns,
  std::ostream &out);

void dump_c_type_header(
  const goto_functionst &src,
  const bool use_system_headers,
  const bool use_all_headers,
  const bool include_harness,
  const namespacet &ns,
  const std::string module,
  std::ostream &out);

void dump_cpp(
  const goto_functionst &src,
  const bool use_system_headers,
  const bool use_all_headers,
  const bool include_harness,
  const namespacet &ns,
  std::ostream &out);

#define OPT_DUMP_C                                                             \
  "(dump-c)(dump-cpp)"                                                         \
  "(dump-c-type-header):"                                                      \
  "(no-system-headers)(use-all-headers)(harness)"

#define HELP_DUMP_C                                                            \
  help_entry("--dump-c", "generate C source")                                  \
    << help_entry(                                                             \
         "--dump-c-type-header m", "generate a C header for types local in m") \
    << help_entry("--dump-cpp", "generate C++ source")                         \
    << help_entry(                                                             \
         "--no-system-headers", "generate C source expanding libc includes")   \
    << help_entry("--use-all-headers", "generate C source with all includes")  \
    << help_entry("--harness", "include input generator in output")

#endif // CPROVER_GOTO_INSTRUMENT_DUMP_C_H
