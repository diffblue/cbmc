#include <assert.h>

struct T
{
  int i;
};

struct U
{
  struct S *s;
  int j;
};

struct S
{
  struct T *t;
  struct U *u;
};

int foo(struct S *s);

int main()
{
  struct T t = {10};
  struct U u = {0, 32};
  struct S s = {&t, &u};
  int res = foo(&s);
  assert(res == 42);
}
