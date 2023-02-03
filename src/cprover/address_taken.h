/*******************************************************************\

Module: Address Taken

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Address Taken

#ifndef CPROVER_CPROVER_ADDRESS_TAKEN_H
#define CPROVER_CPROVER_ADDRESS_TAKEN_H

#include <util/std_expr.h> // IWYU pragma: keep

#include <unordered_set>

std::unordered_set<symbol_exprt, irep_hash>
address_taken(const std::vector<exprt> &);

#endif // CPROVER_CPROVER_ADDRESS_TAKEN_H
