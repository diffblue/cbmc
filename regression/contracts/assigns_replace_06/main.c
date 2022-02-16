#include <assert.h>
#include <stdlib.h>

void foo(char c[]) __CPROVER_assigns(__CPROVER_POINTER_OBJECT(c))
{
}

void bar(char *d) __CPROVER_assigns(*d)
{
}

int main()
{
  char b[4] = {'a', 'b', 'c', 'd'};

  foo(b);

  assert(b[0] == 'a');
  assert(b[1] == 'b');
  assert(b[2] == 'c');
  assert(b[3] == 'd');

  b[1] = '1';
  b[3] = '3';

  bar(b + 3);

  assert(b[0] == 'a');
  assert(b[1] == '1');
  assert(b[2] == 'c');
  assert(b[3] == '3');
}
