/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_RENAME_H
#define CPROVER_UTIL_RENAME_H

//
// automated variable renaming
//

#include "irep.h"

class exprt;
class namespacet;
class symbolt;

void get_new_name(symbolt &symbol,
                  const namespacet &ns);

void get_new_name(
  irep_idt &new_name,
  const namespacet &ns,
  char delimiter = '_');

#endif // CPROVER_UTIL_RENAME_H
