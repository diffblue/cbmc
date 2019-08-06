#include <assert.h>
#include <stdlib.h>

int main(int argc, char **argv)
{
  int x = 10;
  int *array = malloc(sizeof(int) * x);
  array[argc] = 1;
  array[1] = argc;
  assert(array[1] == argc);
}
