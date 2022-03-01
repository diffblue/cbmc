/*******************************************************************\

Module: Instrument Contracts

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Instrument Given Invariants

#ifndef CPROVER_CPROVER_INSTRUMENT_CONTRACTS_H
#define CPROVER_CPROVER_INSTRUMENT_CONTRACTS_H

#include <util/irep.h>
#include <util/optional.h>

class code_with_contract_typet;
class goto_modelt;
class namespacet;

void instrument_contracts(goto_modelt &);

optionalt<code_with_contract_typet>
get_contract(const irep_idt &function_identifier, const namespacet &);

#endif // CPROVER_CPOVER_INSTRUMENT_CONTRACTS_H
