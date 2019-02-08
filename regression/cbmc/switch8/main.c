#include <assert.h>

void main()
{
  switch(0)
  {
    int a;
  default:
    a = 0;
    if(a)
      assert(0);
  }

  switch(1)
  {
    int b;
    b = 42;
  }

  int *p = (void *)0;
  switch(2)
  {
    int c;
  case 3:
    p = &c;
  case 2:
    break;
  }
  assert(p == 0);

  switch(3)
  {
    int d;
  case 3:
    p = &d;
    *p = 42;
    break;
  default:
    d = 1;
    break;
  }
  assert(*p == 42); // invalid dereference

  switch(0)
  {
    int e = 42;
    int f = 42;
  case 0:
    assert(e == 42); // does not hold as the initialisation is unreachable
  default:
    assert(f == 42); // does not hold as the initialisation is unreachable
  }
}
