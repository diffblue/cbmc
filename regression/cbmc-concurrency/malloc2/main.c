#include <stdlib.h>

_Bool set_done;
int *ptr;

void *set_x(void *arg)
{
  *(int *)arg = 10;
  set_done = 1;
}

int main(int argc, char *argv[])
{
  __CPROVER_assume(argc >= sizeof(int));
  ptr = malloc(argc);
  __CPROVER_ASYNC_1: set_x(ptr);
  __CPROVER_assume(set_done);
  assert(*ptr == 10);
  return 0;
}
