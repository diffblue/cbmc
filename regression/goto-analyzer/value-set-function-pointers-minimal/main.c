#include <assert.h>

typedef int (*fptr_t)(int);

int f(int x)
{
  return x + 1;
}
int g(int x)
{
  return x;
}

int main(void)
{
  int nondet_choice;

  fptr_t fun2 = f;
  if(nondet_choice)
    fun2 = g;

  fptr_t fun3;
  if(nondet_choice)
    fun3 = f;
  else
    fun3 = g;

  return 0;
}
