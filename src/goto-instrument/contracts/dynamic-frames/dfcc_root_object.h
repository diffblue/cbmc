/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmasrd@amazon.com

Date: March 2023

\*******************************************************************/

/// \file
/// Utility functions that compute root object expressions for assigns clause
/// targets and LHS expressions.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_ROOT_OBJECT_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_ROOT_OBJECT_H

#include <util/irep.h>

#include <unordered_set>

class exprt;

/// Computes a set of root object expressions from an lvalue or assigns clause
/// target expression. A root object expression is a simpler expression that
/// denotes the object that contains the memory location refered to by the
/// initial expression.
std::unordered_set<exprt, irep_hash> dfcc_root_objects(const exprt &expr);
#endif
