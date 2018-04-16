/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_FIND_MACROS_H
#define CPROVER_UTIL_FIND_MACROS_H

#include <unordered_set>

#include "irep.h"

class exprt;
class namespacet;

typedef unordered_id_sett find_macros_sett;

void find_macros(
  const exprt &src,
  const namespacet &ns,
  find_macros_sett &dest);

#endif // CPROVER_UTIL_FIND_MACROS_H
