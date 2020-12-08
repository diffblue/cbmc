#include <assert.h>

int fun(int other)
{
  if(other > 0)
  {
    int value = fun(other - 1);
    return value + 1;
  }
  else
  {
    return 0;
  }
}

int main(int argc, char *argv[])
{
  int z = fun(0);
  assert(z == 0); // Success because flow-sensitivity blocks the branch
}
