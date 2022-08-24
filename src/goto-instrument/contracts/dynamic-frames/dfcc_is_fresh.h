/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/

/// \file
/// Instruments occurrences of is_fresh/is_freshr predicates in programs
/// encoding requires and ensures clauses of contracts

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_IS_FRESH_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_IS_FRESH_H

#include <util/cprover_prefix.h>
#include <util/std_expr.h>

#include <goto-programs/goto_program.h>

class messaget;
class dfcc_libraryt;

/// Rewrites calls to is_fresh and is_freshr predicates into calls
/// to the library implementation.
class dfcc_is_fresht
{
public:
  /// \param library The contracts instrumentation library
  /// \param log The log to use for messages
  dfcc_is_fresht(dfcc_libraryt &library, messaget &log);

  /// Rewrites calls to is_fresh and is_freshr predicates into calls
  /// to the library implementation in the given program, passing the
  /// given write_set expression as parameter to the library function.
  void rewrite_calls(goto_programt &program, const exprt &write_set);

  /// Rewrites calls to is_fresh and is_freshr predicates into calls
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
  messaget &log;
  const irep_idt is_fresh_id = CPROVER_PREFIX + std::string("is_fresh");
  const irep_idt is_freshr_id = CPROVER_PREFIX + std::string("is_freshr");
};

#endif
