#include <assert.h>

struct A
{
  int x;
  int y;
};

int main(int argc, char **argv)
{
  struct A array[10];
  array[argc].x = 1;
  array[1].x = argc;
  assert(array[1].x == argc);
}
