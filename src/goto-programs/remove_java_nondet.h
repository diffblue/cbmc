/*******************************************************************\

Module: Remove Java Nondet expressions

Author: Reuben Thomas, reuben.thomas@diffblue.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_JAVA_NONDET_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_JAVA_NONDET_H

#include <cstddef> // size_t

class message_handlert;
class symbol_tablet;
class goto_functionst;

/*******************************************************************\

Function: remove_java_nondet

  Inputs:
    message_handler: Object which prints instructions.
    symbol_table: The list of known symbols.
    max_nondet_array_length: The maximum length of new nondet arrays.
    goto_functions: The set of goto programs to modify.

 Purpose: Modify a goto_functionst to replace 'nondet' library functions with
          CBMC-native nondet expressions.

\*******************************************************************/

void remove_java_nondet(
  message_handlert &message_handler,
  symbol_tablet &symbol_table,
  size_t max_nondet_array_length,
  goto_functionst &goto_functions);

#endif
