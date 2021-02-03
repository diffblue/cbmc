#include <assert.h>

int main()
{
  int a = 10;
  int *p = &a;

  *p = 15;

  assert(a == 15);
}
