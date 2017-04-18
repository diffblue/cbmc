/*******************************************************************\

Module: Convert side_effect_expr_nondett expressions

Author: Reuben Thomas, reuben.thomas@diffblue.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_CONVERT_NONDET_H
#define CPROVER_GOTO_PROGRAMS_CONVERT_NONDET_H

#include <cstddef> // size_t

class goto_functionst;
class symbol_tablet;
class message_handlert;

/*******************************************************************\

Function: convert_nondet

  Inputs:
    goto_functions: The set of goto programs to modify.
    symbol_table: The symbol table to query/update.
    message_handler: For error logging.
    max_nondet_array_length: The maximum length of any new arrays.

 Purpose: Replace calls to nondet library functions with an internal
          nondet representation.

\*******************************************************************/

void convert_nondet(
  goto_functionst &goto_functions,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  size_t max_nondet_array_length);

#endif
