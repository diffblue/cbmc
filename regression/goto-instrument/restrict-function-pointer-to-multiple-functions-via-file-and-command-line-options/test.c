#include <assert.h>

typedef int (*fptr_t)(int);

void use_f(fptr_t fptr)
{
  fptr(1);
}

int f(int x)
{
  return x;
}

int g(int x)
{
  return x;
}

int h(int x)
{
  return x;
}

int other(int x)
{
  return x;
}

int main(void)
{
  use_f(f);
  use_f(g);
  use_f(h);
  use_f(other);
}

