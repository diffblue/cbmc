/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

Date:

\*******************************************************************/

#include "signal_catcher.h"
#include "invariant.h"

#if defined(_WIN32)
#else
#include <cstdlib>
#endif

// Here we have an instance of an ugly global object.
// It keeps track of any child processes that we'll kill
// when we are told to terminate. "No child" is indicated by '0'.

#ifdef _WIN32
#else
pid_t child_pid = 0;

void register_child(pid_t pid)
{
  PRECONDITION(child_pid == 0);
  child_pid = pid;
}

void unregister_child()
{
  PRECONDITION(child_pid != 0);
  child_pid = 0;
}
#endif

void install_signal_catcher()
{
#if defined(_WIN32)
#else
  // declare act to deal with action on signal set
  // NOLINTNEXTLINE(readability/identifiers)
  static struct sigaction act;

  act.sa_handler = signal_catcher;
  act.sa_flags = 0;
  sigfillset(&(act.sa_mask));

  // install signal handler
  sigaction(SIGTERM, &act, nullptr);
#endif
}

void remove_signal_catcher()
{
#if defined(_WIN32)
#else
  // declare act to deal with action on signal set
  // NOLINTNEXTLINE(readability/identifiers)
  static struct sigaction act;

  act.sa_handler = SIG_DFL;
  act.sa_flags = 0;
  sigfillset(&(act.sa_mask));

  sigaction(SIGTERM, &act, nullptr);
#endif
}

void signal_catcher(int sig)
{
#if defined(_WIN32)
#else

#if 0
  // kill any children by killing group
  killpg(0, sig);
#else
  // pass on to our child, if any
  if(child_pid != 0)
    kill(child_pid, sig);
#endif

  exit(sig); // should contemplate something from sysexits.h
#endif
}
