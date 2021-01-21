#include <assert.h>

union U {
  int *p;
  unsigned long long p_int;
} u = {.p_int = 42};

int main()
{
  assert(u.p_int == 42);
}
