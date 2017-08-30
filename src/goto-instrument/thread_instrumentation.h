/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_GOTO_INSTRUMENT_THREAD_INSTRUMENTATION_H
#define CPROVER_GOTO_INSTRUMENT_THREAD_INSTRUMENTATION_H

#include <goto-programs/goto_functions.h>

void thread_exit_instrumentation(goto_functionst &);

void mutex_init_instrumentation(const symbol_tablet &, goto_functionst &);

#endif // CPROVER_GOTO_INSTRUMENT_THREAD_INSTRUMENTATION_H
