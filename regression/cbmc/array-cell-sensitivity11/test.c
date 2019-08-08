#include <assert.h>

struct A
{
  int x;
  int y;
};

int main(int argc, char **argv)
{
  struct A array[10];
  int *ptr = argc % 2 ? &argc : &array[0].y;
  *ptr = argc;
  assert(*ptr == argc);
  assert(array[1].y == argc);
}
