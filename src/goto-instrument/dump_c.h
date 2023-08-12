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
  " {y--dump-c} \t generate C source\n"                                        \
  " {y--dump-c-type-header} {um} \t "                                          \
  "generate a C header for types local in {um}\n"                              \
  " {y--dump-cpp} \t generate C++ source\n"                                    \
  " {y--no-system-headers} \t generate C source expanding libc includes\n"     \
  " {y--use-all-headers} \t generate C source with all includes\n"             \
  " {y--harness} \t include input generator in output\n"

#endif // CPROVER_GOTO_INSTRUMENT_DUMP_C_H
