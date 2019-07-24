#include <assert.h>

struct A
{
  int x;
  int y;
};

struct B
{
  struct A a;
};

int main(int argc, char **argv)
{
  struct B b1, b2;
  struct A *aptr = argc % 2 ? &b1.a : &b2.a;
  aptr->x = argc;
  assert(b1.a.x == argc);
  assert(b2.a.x == argc);
}
