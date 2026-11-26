#include <assert.h>

int add(int a, int b)
{
  return a + b;
}

struct fn
{
  int (*f)(int, int);
  int b;
};

// a union whose only member is a byte array, as libc++'s
// aligned_storage<N>::type, used as storage for another object
union buffer
{
  unsigned char data[24];
};

int call(struct fn *self, int *x)
{
  return self->f(*x, self->b);
}

// call's address is taken, so it is a possible target of self->f
int (*taken)(struct fn *, int *) = call;

int main()
{
  union buffer buf;
  struct fn *p = (struct fn *)&buf;
  p->f = add;
  p->b = 10;
  int x = 4;
  assert(call(p, &x) == 14);
  assert(call(p, &x) == 15);
  return 0;
}
