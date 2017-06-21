/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_SIGNAL_CATCHER_H
#define CPROVER_UTIL_SIGNAL_CATCHER_H

void install_signal_catcher();
void remove_signal_catcher();
void signal_catcher(int sig);

#endif // CPROVER_UTIL_SIGNAL_CATCHER_H
