#include <assert.h>

struct A
{
  int x;
  int y;
};

int main(int argc, char **argv)
{
  struct A a1, a2;
  struct A *aptr = argc % 2 ? &a1 : &a2;
  aptr->x = argc;
  aptr->y = argc + 1;
  assert(a1.x == argc);
  assert(a2.x == argc);
}
