#include <util/i2string.h>
#include <cstdlib>
#include <iostream>

#ifdef _MSC_VER
  #include <windows.h>
#else
  #include <csignal>
#endif

class signal_handling {
 public:
static class exceptiont: public std::exception
{
 public:
  virtual const char* what() const throw() {
    return "caught signal";
  }
} exception;

#ifdef _MSC_VER
//should work if CBMC is launched from a console, but does not with CreateProcess/TerminateProcess
  static bool signal_caught = false;
  BOOL WINAPI CCHandler(DWORD);
  BOOL WINAPI kill_handler(DWORD dwType) 
  {
    switch(dwType) {
    case CTRL_C_EVENT:
    case CTRL_BREAK_EVENT:
      signal_caught = true;
      break;
    default:
      break;
    }
    return TRUE;
  }
#else
  static void kill_handler(int s)  {} //just to override default handler
#endif

static void init() {
#ifdef _MSC_VER
  if (!SetConsoleCtrlHandler((PHANDLER_ROUTINE)CCHandler,TRUE)) {
    std::cerr << "Unable to install signal handler!" << std::endl;
    exit(243);
  }
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

static void check_caught_signal() {
#ifdef _MSC_VER
  if(signal_caught) throw exception;
#else
  sigset_t waiting_mask;
  sigpending(&waiting_mask);
  if (sigismember(&waiting_mask, SIGINT) || sigismember(&waiting_mask, SIGTSTP)) {
      throw exception;
  }
#endif
}

};
