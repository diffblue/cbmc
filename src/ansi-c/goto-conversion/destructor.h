/*******************************************************************\

Module: Destructor Calls

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Destructor Calls

#ifndef CPROVER_GOTO_PROGRAMS_DESTRUCTOR_H
#define CPROVER_GOTO_PROGRAMS_DESTRUCTOR_H

#include <util/std_code_base.h>

#include <list>
#include <optional>

class goto_programt;
class namespacet;
class typet;

class code_function_callt
get_destructor(const namespacet &ns, const typet &type);

/// C++ [class.dtor]/13, [basic.life]/5: the elements of an array object of
/// class type with a destructor are destroyed in the reverse order of their
/// construction.  \return the destructor calls for \p array (an array of
/// constant size, possibly multidimensional), or nothing if its elements
/// need no destruction.
std::optional<codet> array_destructor(const namespacet &ns, const exprt &array);

void destruct_locals(
  const std::list<irep_idt> &vars,
  goto_programt &dest,
  const namespacet &ns);

#endif // CPROVER_GOTO_PROGRAMS_DESTRUCTOR_H
