#include <assert.h>

int main()
{
  int unknown;
  int a = 10;
  int b = 10;
  int *p = &a;

  if(unknown)
  {
    b = 15;
    *p = 15;
  }

  assert(*p == b);
}
