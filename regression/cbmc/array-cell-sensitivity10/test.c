#include <assert.h>

struct A
{
  int x;
  int y;
};

int main(int argc, char **argv)
{
  struct A array[10];
  struct A other[2];
  struct A *ptr = argc % 2 ? &other : &array[0];
  ptr[argc].x = 1;
  ptr[1].x = argc;
  assert(ptr[1].x == argc);
  assert(array[1].x == argc);
}
