/*******************************************************************\

Module: Checks for Errors in C and Java Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Checks for Errors in C and Java Programs

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_CHECK_H
#define CPROVER_GOTO_PROGRAMS_GOTO_CHECK_H

class goto_modelt;
class goto_programt;
class optionst;

/// Handle the options "assertions", "built-in-assertions", "assumptions" to
/// remove assertions and assumptions in \p goto_model when these are set to
/// false in \p options.
void transform_assertions_assumptions(
  const optionst &options,
  goto_modelt &goto_model);

/// Handle the options "assertions", "built-in-assertions", "assumptions" to
/// remove assertions and assumptions in \p goto_program when these are set to
/// false in \p options.
void transform_assertions_assumptions(
  const optionst &options,
  goto_programt &goto_program);

#endif // CPROVER_GOTO_PROGRAMS_GOTO_CHECK_H
