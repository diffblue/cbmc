#include <assert.h>

int main(int argc, char **argv)
{
  int array[10];
  int x = 1;
  array[argc] = 1;
  array[x] = argc;
  assert(array[1] == argc);
}
