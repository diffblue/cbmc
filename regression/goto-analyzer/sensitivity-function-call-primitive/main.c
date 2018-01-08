#include <assert.h>
#define ASSERT(x) __CPROVER_assert((x), "assertion " #x)

int bar(int other)
{
  ASSERT(other==4);
  return other + 1;
}

int main(int argc, char *argv[])
{
  int x=3;
  int y=bar(x+1);
  ASSERT(y==5);
}
