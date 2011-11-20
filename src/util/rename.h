/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//
// automated variable renaming
//

#include <irep.h>

class exprt;
class namespacet;
class symbolt;

void get_new_name(symbolt &symbol,
                  const namespacet &ns);
  
void get_new_name(irep_idt &new_name,
                  const namespacet &ns);
  
// true: did nothing
// false: renamed something in the expression

bool rename(exprt &expr, const irep_idt &old_name,
            const irep_idt &new_name);
