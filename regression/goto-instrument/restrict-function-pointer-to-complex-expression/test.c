#include <assert.h>

typedef int (*fptr_t)(int);

fptr_t get_f(void);
fptr_t get_g(void);

void use_fg(int choice, fptr_t fptr, fptr_t gptr)
{
  assert((choice ? fptr : gptr)(10) == 10 + choice);
}

int main(void)
{
  use_fg(0, get_f(), get_g());
  use_fg(1, get_f(), get_g());
}

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
  return x / 2;
}

// Below we take the address of f, g, and h. Thus remove_function_pointers()
// would create a case distinction involving f, g, and h in the function
// use_fg() above.
int always_false_cond = 0;

fptr_t get_f(void)
{
  if(!always_false_cond)
  {
    return f;
  }
  else
  {
    return h;
  }
}

fptr_t get_g(void)
{
  if(!always_false_cond)
  {
    return g;
  }
  else
  {
    return h;
  }
}
