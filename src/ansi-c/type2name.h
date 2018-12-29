/*******************************************************************\

Module: Type Naming for C

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// Type Naming for C

#ifndef CPROVER_ANSI_C_TYPE2NAME_H
#define CPROVER_ANSI_C_TYPE2NAME_H

#include <string>

#include <util/type.h>

class namespacet;

std::string type2name(const typet &type, const namespacet &ns);

#endif // CPROVER_ANSI_C_TYPE2NAME_H
