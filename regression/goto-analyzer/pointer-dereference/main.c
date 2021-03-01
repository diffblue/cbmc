#include <assert.h>

int main()
{
  int a = 10;
  int *p = &a;

  int q = *p;

  assert(q == a);
}
