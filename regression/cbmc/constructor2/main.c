#include <assert.h>
#include <stdlib.h>

#ifdef __GNUC__
int x;

__attribute__((constructor)) void init_heap()
{
  int *p = malloc(sizeof(int));
  free(p);
  x = 42;
}
#endif

int main()
{
#ifdef __GNUC__
  assert(x == 42);
#endif
  return 0;
}
