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
  " --apply-code-contracts       Assume that contracts used in code hold\n"
#define HELP_CHECK_CODE_CONTRACTS \
  " --check-code-contracts       Check that contracts used in code hold\n"
// clang-format on

#endif // CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H
