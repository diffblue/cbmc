#include <assert.h>
#include <stdarg.h>
#define ASSERT(x) __CPROVER_assert((x), "assertion " #x)

int bar(int size, ...)
{
  int total=0;
  va_list args;
  va_start(args, size);
  for(int i = 0; i < size; ++i)
  {
    int val = va_arg(args, int);
    total+=val;
  }

  va_end(args);
  return total;
}

int main(int argc, char *argv[])
{
  int y=bar(4, 1, 2, 2, 1);
  ASSERT(y==6);

  int z=bar(0);
  ASSERT(z==0);
}
