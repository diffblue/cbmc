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

void use_fp(fp_t fp)
{
  assert(fp() == 1);
}

void main()
{
  use_fp(f);
}
