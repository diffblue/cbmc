#include <assert.h>
#define ASSERT(x) __CPROVER_assert((x), "assertion " #x)

int *bar(int *unmodified, int *modifed);

int main(int argc, char *argv[])
{
  int x=3;
  int y=4;
  int *p2x=&x;
  p2x = bar(&x, &y);
  ASSERT(y==5);
  ASSERT(p2x==&y);
  ASSERT(*p2x==5);
}

int *bar(int *unmodified, int *modifed)
{
  ASSERT(*unmodified==3);

  (*modifed) += 1;

  ASSERT(*modifed==5);

  return modifed;
}
