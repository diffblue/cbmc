#include <assert.h>

int f(void)
{
  return 1;
}

int g(void)
{
  return 2;
}

typedef int (*fp_t)(void);

void main()
{
  fp_t fp = f;
  assert(fp() == 1);
}
