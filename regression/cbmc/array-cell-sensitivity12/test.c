#include <assert.h>

struct A
{
  int x;
  int y;
};

int main(int argc, char **argv)
{
  struct A array[10];
  int *ptr = argc % 2 ? &array[0].x : &array[0].y;
  *ptr = argc;
  assert(array[0].y == argc);
}
