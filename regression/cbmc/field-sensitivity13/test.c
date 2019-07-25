#include <assert.h>

struct A
{
  int x;
  int y;
};

struct B
{
  struct A a;
  int z;
};

int main(int argc, char **argv)
{
  struct B b1, b2;
  b1.a.x = argc;
  b1.a.y = argc + 1;
  struct A *aptr = argc % 2 ? &b1.a : &b2.a;
  *aptr = b1.a;
  assert(b2.a.x == argc);
}
