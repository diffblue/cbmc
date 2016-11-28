#ifdef _WIN32
#include <io.h>
#include <fcntl.h>
#else
#include <unistd.h>
#endif

#include <assert.h>

int main()
{
  int filedesc[2];

  #ifdef _WIN32
  int ret=_pipe(filedesc, 1000, O_BINARY);
  #else
  int ret=pipe(filedesc);
  #endif

  __CPROVER_assume(ret==0);

  char data[2] = { 7, 42 };
  ret=write(filedesc[1], data, 2);
  assert(ret==2);

  data[0]=0;
  data[1]=0;
  ret=read(filedesc[0], data, 2);
  assert(ret==2);
  assert(data[0]==7);
  assert(data[1]==31);
  assert(data[1]==42);

  return 0;
}
