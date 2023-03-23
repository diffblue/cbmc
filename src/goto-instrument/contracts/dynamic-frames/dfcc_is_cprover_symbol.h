/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmasrd@amazon.com

Date: March 2023

\*******************************************************************/

/// \file

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_IS_CPROVER_SYMBOL_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_IS_CPROVER_SYMBOL_H

#include <util/irep.h>

/// \return True iff the id starts with CPROVER_PREFIX, `__VERIFIER`, `nondet`
/// or ends with `$object`.
bool dfcc_is_cprover_symbol(const irep_idt &id);

#endif
