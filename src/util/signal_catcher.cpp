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
  sigfillset(&(act.sa_mask));

  // install signal handler
  sigaction(SIGTERM, &act, NULL);
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
  killpg(0, sig);

  exit(sig);
  #endif
}
