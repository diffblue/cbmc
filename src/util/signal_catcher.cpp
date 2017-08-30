/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

Date:

\*******************************************************************/

#include "signal_catcher.h"

#if defined(_WIN32)
#include <process.h>
#else
#include <cstdlib>
#include <csignal>
#endif

#include <vector>

// Here we have an instance of an ugly global object.
// It keeps track of any child processes that we'll kill
// when we are told to terminate.

#ifdef _WIN32
#else
std::vector<pid_t> pids_of_children;
#endif

void install_signal_catcher()
{
  #if defined(_WIN32)
  #else
  // declare act to deal with action on signal set
  // NOLINTNEXTLINE(readability/identifiers)
  static struct sigaction act;

  act.sa_handler=signal_catcher;
  act.sa_flags=0;
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

  act.sa_handler=SIG_DFL;
  act.sa_flags=0;
  sigfillset(&(act.sa_mask));

  sigaction(SIGTERM, &act, nullptr);
  #endif
}

void signal_catcher(int sig)
{
  #if defined(_WIN32)
  #else

  #if 1
  // kill any children by killing group
  killpg(0, sig);
  #else
  // pass on to any children
  for(const auto &pid : pids_of_children)
    kill(pid, sig);
  #endif

  exit(sig); // should contemplate something from sysexits.h
  #endif
}
