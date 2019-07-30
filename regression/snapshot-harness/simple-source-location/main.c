#include <assert.h>

int global_var;

void initialize()
{
  global_var = 1;
}

void checkpoint()
{
}

int foo()
{
  initialize();
  checkpoint();

  assert(global_var == 0);
  //line to be used for init (20)
  assert(global_var == 0);

  return 0;
}

int main()
{
  foo();

  return 0;
}
