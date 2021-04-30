/*******************************************************************\

Module: Destructor Calls

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Destructor Calls

#ifndef CPROVER_GOTO_PROGRAMS_DESTRUCTOR_H
#define CPROVER_GOTO_PROGRAMS_DESTRUCTOR_H

class namespacet;
class typet;

class code_function_callt get_destructor(
  const namespacet &ns,
  const typet &type);

#endif // CPROVER_GOTO_PROGRAMS_DESTRUCTOR_H
