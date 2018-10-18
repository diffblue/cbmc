#include <assert.h>
#include <stdlib.h>

void foo(int argc)
{
  void *x = 0;

  if(argc > 3)
    x = malloc(4 * sizeof(int));
  else
    x = malloc(3 * sizeof(int));
  *(int *)x = 42;

  x = realloc(x, sizeof(int));

  assert(*(int *)x == 42);
}

int main(int argc, char *argv[])
{
__CPROVER_ASYNC_1:
  foo(argc);

  return 0;
}
