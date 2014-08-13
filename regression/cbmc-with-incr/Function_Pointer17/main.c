#include <assert.h>

int bar(int (*start)(void*), void* arg)
{
  return start(arg);
}

struct S
{
  int (*func)(void *);
};

int foo1(void *arg)
{
  struct S *s=arg;
  return bar(s->func, 0);
}

int foo2(void *arg)
{
  return 42;
}

int main()
{
  struct S s;
  s.func=foo1; // make function pointer removal consider foo1
  s.func=foo2;

  assert(foo1(&s)==42);

  return 0;
}
