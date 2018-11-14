#include <assert.h>

struct S
{
  int a;
};

void foo(struct S *x)
{
  x->a = 42;
  assert(x->a == 42);
}

int main()
{
  void *p;
  foo(p);
}
