#include <assert.h>
#include <stdlib.h>

int foo()
{
  return 1;
}

typedef int (*fptr_t)(void);

int main()
{
label_zero:
  assert(1);
  int x;
  int *p;
  goto label_two;
label_one:
  assert(x < 0 || x >= 0);
label_two:
  p = malloc(sizeof(int));
label_three:
  if(foo())
    x = 42;
label_four:
  assert(foo() == 1);
label_five:
  fptr_t fp = foo;
  assert(fp() == 1);
label_six:
  return *p;
}
