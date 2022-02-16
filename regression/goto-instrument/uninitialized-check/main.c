#include <stdlib.h>

int globals_are_actually_initialized; // See ISO-9899!

int main(int argc, char **argv)
{
  int definitely_uninitialized;
  int maybe_uninitialized;
  int actually_initialized;

  if(argc > 1)
  {
    maybe_uninitialized = 1;
  }

  if(argc <= 3)
  {
    actually_initialized = 0;
  }
  if(argc >= 4)
  {
    actually_initialized = 1;
  }

  int *heap_variables_uninitialized = malloc(sizeof(int));

  return definitely_uninitialized + maybe_uninitialized + actually_initialized +
         globals_are_actually_initialized + *heap_variables_uninitialized;
}
