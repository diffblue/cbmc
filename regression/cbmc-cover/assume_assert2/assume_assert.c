#include <assert.h>

int main(int argc, char *argv[])
{
  int a;

  if(a > 0)
  {
    assert(a > 0);
  }
  else if(a < 0)
  {
    __CPROVER_assume(a >= 0);
    assert(a < 0);
  }
  else
  {
    assert(a == 0);
  }
}
