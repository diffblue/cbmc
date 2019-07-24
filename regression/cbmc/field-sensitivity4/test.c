#include <assert.h>

struct A
{
  int x;
  int y;
};

int main(int argc, char **argv)
{
  struct A a;
  int *field = argc % 2 ? &a.x : &a.y;
  *field = argc;
  assert(a.x == argc);
  assert(a.y == argc);
}
