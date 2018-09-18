/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_SIGNAL_CATCHER_H
#define CPROVER_UTIL_SIGNAL_CATCHER_H

void install_signal_catcher();
void remove_signal_catcher();
void signal_catcher(int sig);

#ifndef _WIN32
#include <csignal>
void register_child(pid_t);
void unregister_child();
#endif

#endif // CPROVER_UTIL_SIGNAL_CATCHER_H
