/*******************************************************************\

Module: Abstraction for malloc

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_DYNAMIC_MEMORY_H
#define CPROVER_GOTO_PROGRAMS_DYNAMIC_MEMORY_H

#include <namespace.h>

exprt deallocated(const namespacet &ns, const exprt &pointer);
exprt dynamic_size(const namespacet &ns, const exprt &pointer);
exprt pointer_object_has_type(const namespacet &ns, const exprt &pointer, const typet &type);
exprt dynamic_object(const exprt &pointer);

#endif
