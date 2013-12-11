#include "signal_catcher.h"

#if defined(_WIN32)
  /*
//should work if CBMC is launched from a console, but does not with CreateProcess/TerminateProcess
  bool signal_catchert::signal_caught;
  BOOL signal_catchert::kill_handler(DWORD s) 
  {
    switch(s) {
    case CTRL_C_EVENT:
    case CTRL_BREAK_EVENT:
      signal_caught = true;
      break;
    default:
      break;
    }
    return TRUE;
    }*/
#else
  void signal_catchert::kill_handler(int s)  {} //just to override default handler
#endif

void signal_catchert::init() {
#if defined(_WIN32)
  /*
  signal_caught = false;
  if (!SetConsoleCtrlHandler((PHANDLER_ROUTINE)kill_handler,TRUE)) {
    std::cerr << "Unable to install signal handler!" << std::endl;
    exit(243);
  }
  */
#else
  struct sigaction sa;
  sa.sa_handler = kill_handler;
  sigemptyset(&sa.sa_mask);
  sigaddset(&sa.sa_mask, SIGINT);
  sigaddset(&sa.sa_mask, SIGTSTP); 
  sigprocmask(SIG_SETMASK, &sa.sa_mask, NULL); //block signals, 
                                               //we only want to check only at certain points 
  sa.sa_flags = 0;
  if (sigaction(SIGINT, &sa, NULL) == -1) {
    std::cerr << "Unable to install signal handler!" << std::endl;
    exit(243);
  }
#endif
}

void signal_catchert::check_caught_signal() {
#if defined(_WIN32)
  //  if(signal_caught) throw exceptiont();
#else
  sigset_t waiting_mask;
  sigpending(&waiting_mask);
  if (sigismember(&waiting_mask, SIGINT) || sigismember(&waiting_mask, SIGTSTP)) {
     killpg(0, SIGINT);
     throw exceptiont();
  }
#endif
}
