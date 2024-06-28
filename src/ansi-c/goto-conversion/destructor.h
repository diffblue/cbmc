/*******************************************************************\

Module: Destructor Calls

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Destructor Calls

#ifndef CPROVER_GOTO_PROGRAMS_DESTRUCTOR_H
#define CPROVER_GOTO_PROGRAMS_DESTRUCTOR_H

#include <util/irep.h>

#include <list>

class goto_programt;
class namespacet;
class typet;

class code_function_callt
get_destructor(const namespacet &ns, const typet &type);

void destruct_locals(
  const std::list<irep_idt> &vars,
  goto_programt &dest,
  const namespacet &ns);

#endif // CPROVER_GOTO_PROGRAMS_DESTRUCTOR_H
