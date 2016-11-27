/*******************************************************************\

Module:

Author:

Date:

\*******************************************************************/

#if defined(_WIN32)

#else
#include <signal.h>
#include <cstdlib>

#include <csignal>
#endif

#include "signal_catcher.h"

pid_t child_pgid;

/*******************************************************************\

Function: install_signal_catcher

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void install_signal_catcher()
{
  #if defined(_WIN32)
  #else
  // declare act to deal with action on signal set
  static struct sigaction act;

  act.sa_handler=signal_catcher;
  act.sa_flags=0;
  sigemptyset(&(act.sa_mask));

  // install signal handler
  sigaction(SIGHUP, &act, NULL);
  sigaction(SIGINT, &act, NULL);
  sigaction(SIGTERM, &act, NULL);
  sigaction(SIGALRM, &act, NULL);
  sigaction(SIGUSR1, &act, NULL);
  sigaction(SIGUSR2, &act, NULL);
  #endif
}

/*******************************************************************\

Function: signal_catcher

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void signal_catcher(int sig)
{
  #if defined(_WIN32)
  #else
  // kill any children by killing group
  killpg(child_pgid, sig);

  exit(sig);
  #endif
}
