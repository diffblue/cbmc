/*******************************************************************\

Module: Unwind loops in static initializers

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Unwind loops in static initializers

#ifndef CPROVER_JAVA_BYTECODE_JAVA_ENUM_STATIC_INIT_UNWIND_HANDLER_H
#define CPROVER_JAVA_BYTECODE_JAVA_ENUM_STATIC_INIT_UNWIND_HANDLER_H

#include <goto-symex/goto_symex_state.h>

#include <util/symbol_table.h>
#include <util/threeval.h>

tvt java_enum_static_init_unwind_handler(
  const call_stackt &context,
  unsigned loop_number,
  unsigned unwind_count,
  unsigned &unwind_max,
  const symbol_tablet &symbol_table);

#endif // CPROVER_JAVA_BYTECODE_JAVA_ENUM_STATIC_INIT_UNWIND_HANDLER_H
