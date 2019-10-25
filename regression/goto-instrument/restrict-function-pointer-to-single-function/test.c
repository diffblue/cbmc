#include <assert.h>

typedef int (*fptr_t)(int);

fptr_t get_f(void);

void use_f(fptr_t fptr)
{
  assert(fptr(10) == 11);
}

int main(void)
{
  use_f(get_f());
}

int f(int x)
{
  return x + 1;
}
int g(int x)
{
  return x;
}

// this is just here to distinguish the behavior from FP removal, which'd include
// only f if we didn't reference g anywhere.
int g_always_false_cond = 0;

fptr_t get_f(void)
{
  if(!g_always_false_cond)
  {
    return f;
  }
  else
  {
    return g;
  }
}
