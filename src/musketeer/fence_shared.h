/*******************************************************************\

Module: (naive) Fence insertion

Purpose: fences all the shared or volatile-declared variables

Author: Vincent Nimal 

\*******************************************************************/

#ifndef CPROVER_FENCE_SHARED_H
#define CPROVER_FENCE_SHARED_H

class value_setst;
class goto_functionst;
class symbol_tablet;
class message_handlert;

/* finds all the shared variables (including static, global and dynamic) */
void fence_all_shared(
  message_handlert& message_handler,
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions);

/* finds all the shared variables (including static, global and dynamic) */
void fence_all_shared_aeg(
  message_handlert& message_handler,
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions);

/* finds all the volatile-declared variables */
void fence_volatile(
  message_handlert& message_handler,
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions);

#endif
