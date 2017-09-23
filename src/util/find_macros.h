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

using find_macros_sett = std::unordered_set<irep_idt, irep_id_hash>;

void find_macros(
  const exprt &src,
  const namespacet &ns,
  find_macros_sett &dest);

#endif // CPROVER_UTIL_FIND_MACROS_H
