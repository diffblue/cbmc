/*******************************************************************\

Module: Replace Java Nondet expressions

Author: Reuben Thomas, reuben.thomas@diffblue.com

\*******************************************************************/

/// \file
/// Replace Java Nondet expressions

#ifndef CPROVER_GOTO_PROGRAMS_REPLACE_JAVA_NONDET_H
#define CPROVER_GOTO_PROGRAMS_REPLACE_JAVA_NONDET_H

class goto_functionst;

/// Replace calls to nondet library functions with an internal nondet
/// representation.
/// \param goto_functions: The set of goto programs to modify.
void replace_java_nondet(goto_functionst &goto_functions);

#endif
