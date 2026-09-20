#include <assert.h>

int free_called = 0;

void free(void *ptr)
{
  free_called = 1;
}

int main()
{
  int x;
  free(&x);
  assert(free_called == 1);
  return 0;
}
