/*******************************************************************\

Module: Output of the program (SSA) constraints

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Output of the program (SSA) constraints

#ifndef CPROVER_GOTO_SYMEX_SHOW_PROGRAM_H
#define CPROVER_GOTO_SYMEX_SHOW_PROGRAM_H

class namespacet;
class symex_target_equationt;

void show_program(const namespacet &ns, const symex_target_equationt &equation);

#endif // CPROVER_GOTO_SYMEX_SHOW_PROGRAM_H
