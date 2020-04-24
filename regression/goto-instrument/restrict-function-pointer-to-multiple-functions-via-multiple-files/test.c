#include <assert.h>

typedef int (*fptr_t)(int);

fptr_t get_f(void);

void use_f(fptr_t fptr)
{
  assert(fptr(10) >= 10);
}

void select_f(void);
void select_g(void);
void select_h(void);

int main(void)
{
  select_f();
  use_f(get_f());
  select_g();
  use_f(get_f());
  select_h();
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

int h(int x)
{
  return x - 1;
}

int select_function = 0;

void select_f(void)
{
  select_function = 0;
}

void select_g(void)
{
  select_function = 1;
}

void select_h(void)
{
  select_function = 2;
}

fptr_t get_f(void)
{
  if(select_function == 0)
  {
    return f;
  }
  else if(select_function == 1)
  {
    return g;
  }
  else
  {
    return h;
  }
}
