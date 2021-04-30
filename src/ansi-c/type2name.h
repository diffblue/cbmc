/*******************************************************************\

Module: Type Naming for C

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// Type Naming for C

#ifndef CPROVER_ANSI_C_TYPE2NAME_H
#define CPROVER_ANSI_C_TYPE2NAME_H

#include <string>

class namespacet;
class typet;

std::string type2name(const typet &type, const namespacet &ns);

/**
 * Constructs a string describing the given type, which can be used as part of
 * a `C` identifier. The resulting identifier is not guaranteed to uniquely
 * identify the type in all cases.
 * @param type Internal representation of the type to describe.
 * @param ns Namespace for looking up any types on which the `type` parameter
 *   depends.
 * @return An identifying string which can be used as part of a `C` identifier.
 */
std::string type_to_partial_identifier(const typet &type, const namespacet &ns);

#endif // CPROVER_ANSI_C_TYPE2NAME_H
