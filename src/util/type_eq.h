/*******************************************************************\

Module: Type equality

Author: Daniel Kroening, kroening@kroening.com
        Maria Svorenova, maria.svorenova@diffblue.com

\*******************************************************************/

/// \file
/// Type equality

#ifndef CPROVER_UTIL_TYPE_EQ_H
#define CPROVER_UTIL_TYPE_EQ_H

#include "deprecate.h"

class namespacet;
class typet;

DEPRECATED("Use == instead")
bool type_eq(const typet &type1, const typet &type2, const namespacet &ns);

#endif // CPROVER_UTIL_TYPE_EQ_H
