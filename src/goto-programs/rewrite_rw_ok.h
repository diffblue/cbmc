/*******************************************************************\

Module: Rewrite {r,w,rw}_ok expressions as required by symbolic execution

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Rewrite r/w/rw_ok expressions to ones including prophecy variables recording
/// the state.

#ifndef CPROVER_GOTO_PROGRAMS_REWRITE_RW_OK_H
#define CPROVER_GOTO_PROGRAMS_REWRITE_RW_OK_H

class goto_modelt;

/// Replace all occurrences of `r_ok_exprt`, `w_ok_exprt`, `rw_ok_exprt`,
/// `pointer_in_range_exprt` by their prophecy variants
/// `prophecy_r_or_w_ok_exprt` and `prophecy_pointer_in_range_exprt`,
/// respectively.
/// Each analysis may choose to natively support `r_ok_exprt` etc. (like
/// `cprover_parse_optionst` does) or may instead require the expression to be
/// lowered to other primitives (like `goto_symext`).
void rewrite_rw_ok(goto_modelt &);

#endif // CPROVER_GOTO_PROGRAMS_REWRITE_RW_OK_H
