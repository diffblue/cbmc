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
  long long *field = argc % 2 ? (char *)&a1.y : (char *)&a2.z;
  *field = argc;
  assert(a1.y == argc);
  assert(a2.z == argc);
}
