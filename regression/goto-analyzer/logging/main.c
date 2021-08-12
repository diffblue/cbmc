#include <assert.h>

int global;

int f00(int x)
{
  return global + x;
}

int main(void)
{
  int local;
  unsigned int nondet;

  local = 1;
  global = 1;

  assert(local == global);

  if(nondet)
  {
    local = 2;
  }
  if(nondet)
  {
    global = 2;
  }

  assert(local == global);

  do
  {
    local = 3;
    global = 3;
  } while(nondet-- > 0);

  assert(local == global);

  local = 4;
  global = 4;

  local = f00(1);
  global = f00(1);

  assert(local == global);

  return 0;
}
