#include <assert.h>

int f(void)
{
  return 1;
}
int g(void)
{
  return 2;
}
int h(void)
{
  return 3;
}

typedef int (*fptr_t)(void);

void use_f(fptr_t fptr)
{
  assert(fptr() == 2);
}

int nondet_int(void);

fptr_t g_fptr;
int main(void)
{
  int cond = nondet_int();
  if(cond)
  {
    g_fptr = f;
  }
  else
  {
    g_fptr = h;
  }
  int res = g_fptr();
  assert(res == 1 || res == 3);
  use_f(g);
  fptr_t fptr = f;
  assert(fptr() == 1);
  return 0;
}
