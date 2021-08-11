#include <assert.h>

int global;

int main(void)
{
  int local;
  unsigned int nondet;

  local = 1;
  global = 1;

  if(nondet == 0)
  {
    local = 2;
  }
  if(nondet == 0)
  {
    global = 2;
  }

  assert(local == global);
}
