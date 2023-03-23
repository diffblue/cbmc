/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmasrd@amazon.com

Date: March 2023

\*******************************************************************/

/// \file
/// Utility function that computes the set of identifiers an expression is based
/// on.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_BASE_IDENTS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_BASE_IDENTS_H

#include <util/irep.h>
#include <util/optional.h>

#include <set>

class exprt;

/// \return the set of base identifiers accessed in \p expr, or `nullopt`
/// if \p expr contains a `dereference` or `address_of` operator that cannot be
/// directly resolved by simple pattern matching rules.
///
/// \details
/// For example, these cases succeed:
/// - `dfcc_base_idents(array[i]) = {array}`.
/// - `dfcc_base_idents(struct.member) = {struct}`.
/// - `dfcc_base_idents(struct.array_member[i]) = {struct}`.
/// - `dfcc_base_idents(c ? array1[i]:struct.m) = {array, struct}`.
/// - `dfcc_base_idents(*(&array[i])) = {array}`.
///
/// And this case would return `nullopt`:
/// - `dfcc_base_idents(*(&array[0] + i))) = nullopt`.
///
optionalt<std::set<irep_idt>> dfcc_base_idents(const exprt &expr);
#endif
