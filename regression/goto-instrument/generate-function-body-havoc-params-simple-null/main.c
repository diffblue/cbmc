#include <assert.h>
#include <stdlib.h>

void func(int *p);

void main()
{
  int *p;
  p = NULL;

  func(p);
}
