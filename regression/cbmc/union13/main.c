#include <assert.h>
#include <stdint.h>

int main()
{
  union {
    intptr_t i;
    int *p;
  } u;
  u.i = 0;
  assert(u.p == 0);
}
