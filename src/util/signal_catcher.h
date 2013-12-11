#include <util/i2string.h>
#include <cstdlib>
#include <iostream>

#if defined(_WIN32)
//  #include <windows.h>
#else
  #include <csignal>
#endif

class signal_catchert {
 public:
class exceptiont: public std::exception
{
 public:
  virtual const char* what() const throw() {
    return "caught signal";
  }
};

#if defined(_WIN32)
  /*
  static bool signal_caught;
  static BOOL kill_handler(DWORD s);
  */
#else
 static void kill_handler(int s);
#endif

 static void init();
 static void check_caught_signal();

};
