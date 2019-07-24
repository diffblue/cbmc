#include <assert.h>
#include <stdlib.h>

int main(int argc, char **argv)
{
  int *array = malloc(sizeof(int) * 10);
  array[argc] = 1;
  array[1] = argc;
  assert(array[1] == argc);
}
