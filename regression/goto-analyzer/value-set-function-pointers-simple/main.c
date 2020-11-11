#include <assert.h>

typedef int (*fptr_t)(int);
fptr_t fun_global, fun_global_show;

int f(int x)
{
  return x + 1;
}
int g(int x)
{
  return x;
}
int h(int x)
{
  return x - 1;
}

int main(void)
{
  int nondet_choice;

  // Variable never written to should be top
  fptr_t fun0;
  fun0(5);

  fptr_t fun1 = f;
  fun1(5);

  fptr_t fun2 = f;
  if(nondet_choice)
    fun2 = g;
  fun2(5);
  fptr_t fun2_show = fun2;

  fptr_t fun3;
  if(nondet_choice)
    fun3 = f;
  else
    fun3 = g;
  fun3(5);
  fptr_t fun3_show = fun3;

  // Global variable
  if(nondet_choice)
    fun_global = f;
  else
    fun_global = g;
  fun_global(5);
  fun_global_show = fun_global;

  return 0;
}
