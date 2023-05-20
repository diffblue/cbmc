/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmasrd@amazon.com

Date: March 2023

\*******************************************************************/

/// \file

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_IS_CPROVER_SYMBOL_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_IS_CPROVER_SYMBOL_H

#include <util/irep.h>

/// Returns `true` iff id is one of the known CPROVER functions or starts with
/// `__VERIFIER` or `nondet`.
bool dfcc_is_cprover_function_symbol(const irep_idt &id);

/// Returns `true` iff the symbol is one of the known CPROVER static
/// instrumentation variables or ends with `$object` and represents an
/// auto-generated object following a pointer dereference.
bool dfcc_is_cprover_static_symbol(const irep_idt &id);

#endif
