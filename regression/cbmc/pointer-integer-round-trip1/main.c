#include <assert.h>
#include <stdint.h>

union U
{
  char *p;
  uintptr_t i;
};

int main()
{
  union U u;
  u.i = 0x1234;
  char *p = u.p;
  uintptr_t i = (uintptr_t)p;
  char *q = (char *)i;
  assert(q == p);
}
