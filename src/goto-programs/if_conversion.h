/*******************************************************************\

Module: If-conversion of side-effect-free conditional assignments

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// If-conversion of side-effect-free conditional assignments
///
/// Replace control-flow branches whose then/else regions consist solely of
/// assignments with branch-free guarded (conditional-expression) assignments,
/// e.g. rewrite the GOTO program for
/// \code
///   if(cond) x = e;
/// \endcode
/// into
/// \code
///   x = cond ? e : x;
/// \endcode
/// removing the GOTO branch. This avoids forking the symbolic-execution path
/// tree in `--paths` mode at trivial control flow (such as the bookkeeping in
/// the built-in CPROVER library), which would otherwise cause exponential
/// path explosion.
///
/// The transformation must run before goto_check, so that the per-operand
/// safety checks of the generated conditional expressions remain guarded by
/// the branch condition (see goto_check_ct::check_rec_if); it is therefore
/// sound even when the assignments dereference pointers, divide, or overflow.

#ifndef CPROVER_GOTO_PROGRAMS_IF_CONVERSION_H
#define CPROVER_GOTO_PROGRAMS_IF_CONVERSION_H

#include <util/irep.h>

#include <cstddef>

class goto_modelt;
class goto_programt;
class message_handlert;
class namespacet;
class symbol_table_baset;

/// Apply if-conversion to all functions of \p goto_model. \return the number
/// of branches that were removed.
std::size_t if_conversion(goto_modelt &goto_model, message_handlert &);

/// Apply if-conversion to a single \p goto_program, creating any fresh guard
/// variables in \p symbol_table with mode \p mode. Does not run remove_skip or
/// update targets; the caller is responsible for doing so. \return the number
/// of branches that were removed.
std::size_t if_conversion(
  goto_programt &goto_program,
  symbol_table_baset &symbol_table,
  const irep_idt &mode,
  const namespacet &ns);

#endif // CPROVER_GOTO_PROGRAMS_IF_CONVERSION_H
