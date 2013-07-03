#include <unistd.h>
#include <assert.h>

int main()
{
  int filedesc[2];
  int ret=pipe(filedesc);
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
