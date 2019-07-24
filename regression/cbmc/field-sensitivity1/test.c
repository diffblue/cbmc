#include <assert.h>

struct A
{
  int x;
  int y;
};

int main(int argc, char **argv)
{
  struct A a;
  a.x = argc;
  a.y = argc + 1;
  assert(a.x == argc);
}
