/*******************************************************************\

Module: Unused function removal

Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_GOTO_PROGRAMS_REMOVE_FUNCTIONS_H_
#define _CPROVER_GOTO_PROGRAMS_REMOVE_FUNCTIONS_H_

#include <message.h>

#include <goto-programs/goto_functions.h>

void remove_unused_functions( 
  goto_functionst &functions,
  message_handlert &message_handler);

void find_used_functions(
  const irep_idt &current,
  goto_functionst &functions,
  std::set<irep_idt> &seen);

#endif /*_CPROVER_LOOPFROG_REMOVE_FUNCTIONS_H_*/
