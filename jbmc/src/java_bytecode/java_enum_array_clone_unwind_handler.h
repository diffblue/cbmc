/*******************************************************************\

Module: Unwind loops in array clone for enums

Author: Diffblue

\*******************************************************************/

/// \file
/// Unwind loops in array.clone for enums

#ifndef CPROVER_JAVA_BYTECODE_JAVA_ENUM_ARRAY_CLONE_UNWIND_HANDLER_H
#define CPROVER_JAVA_BYTECODE_JAVA_ENUM_ARRAY_CLONE_UNWIND_HANDLER_H

#include <util/symbol_table.h>
#include <util/threeval.h>

tvt java_enum_array_clone_unwind_handler(
  const irep_idt &function_id,
  unsigned loop_number,
  unsigned unwind_count,
  unsigned &unwind_max,
  const symbol_tablet &symbol_table);

#endif // CPROVER_JAVA_BYTECODE_JAVA_ENUM_ARRAY_CLONE_UNWIND_HANDLER_H
