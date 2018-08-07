/*******************************************************************\

Module: Verify and use annotated invariants and pre/post-conditions

Author: Michael Tautschnig

Date: February 2016

\*******************************************************************/

/// \file
/// Verify and use annotated invariants and pre/post-conditions

#ifndef CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H
#define CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H

class goto_modelt;

void apply_code_contracts(goto_modelt &);
void check_code_contracts(goto_modelt &);

// clang-format off
#define HELP_APPLY_CODE_CONTRACTS \
  " --apply-code-contracts       Assume (without checking) that the contracts used in code hold\n" \
  "                              This will use __CPROVER_requires, __CPROVER_ensures,\n" \
  "                              and __CPROVER_loop_invariant as assumptions in order to avoid\n" \
  "                              checking code that is assumed to satisfy a specification.\n"
#define HELP_CHECK_CODE_CONTRACTS \
  " --check-code-contracts       Assume (with checking) that the contracts used in code hold.\n" \
  "                              This differs from --apply-code-contracts in that in addition to\n" \
  "                              assuming specifications, it checks that they are correct.\n"
// clang-format on

#endif // CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H
