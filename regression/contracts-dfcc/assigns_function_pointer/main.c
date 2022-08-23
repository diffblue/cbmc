#include <assert.h>
#include <stddef.h>

int x;

struct fptr_t
{
  void (*f)();
};

void foo()
{
  x = 1;
}

void foofoo()
{
  x = 2;
}

void bar(struct fptr_t *s, void (**f)()) __CPROVER_assigns(s->f, *f)
{
  s->f = &foo;
  *f = &foofoo;
}

int main()
{
  x = 0;
  struct fptr_t s;
  void (*f)();
  bar(&s, &f);
  s.f();
  assert(x == 1);
  f();
  assert(x == 2);
  return 0;
}
