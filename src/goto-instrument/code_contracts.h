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

#endif // CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H
