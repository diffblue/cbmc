/*******************************************************************\

Module: Checks for Errors in C/C++ Programs

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Checks for Errors in C/C++ Programs

#ifndef CPROVER_CPROVER_C_SAFETY_CHECKS_H
#define CPROVER_CPROVER_C_SAFETY_CHECKS_H

class goto_modelt;

void c_safety_checks(goto_modelt &);
void no_assertions(goto_modelt &);

#endif // CPROVER_CPROVER_C_SAFETY_CHECKS_H
