#include <stdlib.h>

int **fun(void) {
  int **Array = malloc(2 * sizeof(int *));

  Array[0] = malloc(sizeof(int));
  *Array[0] = 32;
  Array[1] = malloc(sizeof(int));
  *Array[1] = 64;

  return Array;
}

int main(int argc, char *argv[])
{
  int **array;
  array = fun();
  return 0;
}
