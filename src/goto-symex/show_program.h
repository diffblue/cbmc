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

/// Print the steps of \p equation on the standard output.
///
/// For each step, prints the location, then if the step is an assignment,
/// assertion, assume, constraint, shared read or shared write:
/// prints an instruction counter, followed by the instruction type, and the
/// current guard if it is not equal to true.
/// \param ns: namespace
/// \param equation: SSA form of the program
void show_program(const namespacet &ns, const symex_target_equationt &equation);

#endif // CPROVER_GOTO_SYMEX_SHOW_PROGRAM_H
