/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_THREAD_EXIT_INSTRUMENTATION_H
#define CPROVER_THREAD_EXIT_INSTRUMENTATION_H

#include <goto-programs/goto_functions.h>

void thread_exit_instrumentation(goto_functionst &);

void mutex_init_instrumentation(const symbol_tablet &, goto_functionst &);

#endif
