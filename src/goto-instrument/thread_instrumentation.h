/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_GOTO_INSTRUMENT_THREAD_INSTRUMENTATION_H
#define CPROVER_GOTO_INSTRUMENT_THREAD_INSTRUMENTATION_H

class goto_modelt;

void thread_exit_instrumentation(goto_modelt &);
void mutex_init_instrumentation(goto_modelt &);

#endif // CPROVER_GOTO_INSTRUMENT_THREAD_INSTRUMENTATION_H
