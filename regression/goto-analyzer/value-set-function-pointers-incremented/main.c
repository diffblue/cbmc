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
  // This line is needed so that g is considered as a possibility for the TOP
  // value
  fptr_t dummy = g;

  // function pointer incremented should be top
  fptr_t fun_incremented = f;
  ++fun_incremented;
  fun_incremented(5);
  fptr_t fun_incremented_show = fun_incremented;
}
