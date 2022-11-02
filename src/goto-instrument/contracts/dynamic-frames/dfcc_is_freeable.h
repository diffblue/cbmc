/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/

/// \file
/// Instruments occurrences of is_freeable predicates in programs
/// encoding requires and ensures clauses of contracts

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_IS_FREEABLE_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_IS_FREEABLE_H

#include <util/message.h>

#include <goto-programs/goto_program.h>

class goto_modelt;
class message_handlert;
class dfcc_libraryt;
class exprt;

/// Rewrites calls to is_freeable and was_freed predicates in goto programs
/// encoding pre and post conditions.
class dfcc_is_freeablet
{
public:
  /// \param library the contracts instrumentation library
  /// \param message_handler used for messages
  dfcc_is_freeablet(dfcc_libraryt &library, message_handlert &message_handler);

  /// Rewrites calls to is_freeable and was_freed predicates into calls
  /// to the library implementation in the given program, passing the
  /// given write_set expression as parameter to the library function.
  void rewrite_calls(goto_programt &program, const exprt &write_set);

  /// Rewrites calls to is_fresh predicates into calls
  /// to the library implementation in the given program between
  /// first_instruction (included) and last_instruction (excluded), passing the
  /// given write_set expression as parameter to the library function.
  void rewrite_calls(
    goto_programt &program,
    goto_programt::targett first_instruction,
    const goto_programt::targett &last_instruction, // excluding the last
    const exprt &write_set);

protected:
  dfcc_libraryt &library;
  message_handlert &message_handler;
  messaget log;
};

#endif
