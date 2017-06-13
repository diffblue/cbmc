/*******************************************************************\

Module: Replace Java Nondet expressions

Author: Reuben Thomas, reuben.thomas@diffblue.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_REPLACE_JAVA_NONDET_H
#define CPROVER_GOTO_PROGRAMS_REPLACE_JAVA_NONDET_H

class goto_functionst;

/*******************************************************************\

Function: replace_java_nondet

  Inputs:
    goto_functions: The set of goto programs to modify.

 Purpose: Replace calls to nondet library functions with an internal
          nondet representation.

\*******************************************************************/

void replace_java_nondet(goto_functionst &goto_functions);

#endif
