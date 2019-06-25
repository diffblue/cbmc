/*******************************************************************\

Module: Dump C from Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Dump C from Goto Program

#ifndef CPROVER_GOTO_INSTRUMENT_DUMP_C_H
#define CPROVER_GOTO_INSTRUMENT_DUMP_C_H

#include <goto-programs/goto_functions.h>

void dump_c(
  const goto_functionst &src,
  const bool use_system_headers,
  const bool use_all_headers,
  const bool include_harness,
  const namespacet &ns,
  // This argument specifies the name of the function to dump. It is
  // used for stub generation. If it is NULL, dump_c operates in the
  // standard way.
  const optionalt<irep_idt> stub_name,
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
  const optionalt<irep_idt> stub_name,
  std::ostream &out);

#endif // CPROVER_GOTO_INSTRUMENT_DUMP_C_H
