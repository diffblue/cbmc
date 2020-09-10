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
class optionst;
class ui_message_handlert;

/// Print the steps of \p equation on the standard output.
///
/// For each step, prints the location, then if the step is an assignment,
/// assertion, assume, constraint, shared read or shared write:
/// prints an instruction counter, followed by the instruction type, and the
/// current guard if it is not equal to true.
/// \param ns: namespace
/// \param equation: SSA form of the program
void show_program(const namespacet &ns, const symex_target_equationt &equation);

/// Count and display all byte extract and byte update operations from equation
/// on standard output or file.
/// The name of the output file is given by the `outfile` option from
/// \p options, the standard output is used if it is not provided.
/// The format is either JSON or plain text depending on \p ui_message_handler;
/// XML is not supported.
/// For each step, if it's a byte extract or update, print location, ssa
/// expression and compute number of extracts/updates in total in the equation.
/// \param options: parsed options
/// \param ui_message_handler: ui message handler
/// \param ns: namespace
/// \param equation: SSA form of the program
void show_byte_ops(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  const namespacet &ns,
  const symex_target_equationt &equation);

#endif // CPROVER_GOTO_SYMEX_SHOW_PROGRAM_H
