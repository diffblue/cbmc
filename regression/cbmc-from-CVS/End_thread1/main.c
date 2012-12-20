#ifdef _WIN32

#include "windows.h"

#else

void pthread_exit(void *value_ptr);

#endif

int main()
{
  int i;

  if(i==100)
  {
    #ifdef _WIN32
    ExitThread(0);
    #else
    pthread_exit(0);
    #endif
  }

  assert(i!=100);
}

