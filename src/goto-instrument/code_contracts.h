/*******************************************************************\

Module: Verify and use annotated invariants and pre/post-conditions

Author: Michael Tautschnig

Date: February 2016

\*******************************************************************/

/// \file
/// Verify and use annotated invariants and pre/post-conditions

#ifndef CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H
#define CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H

#include <list>
#include <string>

class goto_modelt;

void code_contracts(goto_modelt &);

void assert_ensures(goto_modelt &goto_model, std::list<std::string> functions);

#endif // CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H
