/*******************************************************************\

Module: Verify and use annotated invariants and pre/post-conditions

Author: Michael Tautschnig

Date: February 2016

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H
#define CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H

class goto_functionst;
class symbol_tablet;

void code_contracts(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions);

#endif // CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H
