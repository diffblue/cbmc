#include <assert.h>

struct A
{
  int x;
  int y;
};

int main(int argc, char **argv)
{
  struct A a1, a2;
  a1.x = argc;
  a1.y = argc + 1;
  struct A *aptr = argc % 2 ? &a1 : &a2;
  *aptr = a1;
  assert(a2.x == argc);
}
