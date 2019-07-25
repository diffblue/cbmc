#include <assert.h>

struct A
{
  int x;
  int y;
  int z;
};

int main(int argc, char **argv)
{
  struct A a1, a2;
  int *field = argc % 2 ? &a1.y : &a2.z;
  *field = argc;
  assert(a1.y == argc);
  assert(a2.z == argc);
}
