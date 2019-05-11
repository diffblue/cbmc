// f is set to 0 -> does not point to either f1 or f2
#include <assert.h>

typedef int (*f_ptr)(int);

extern f_ptr f;

int f1(int j);
int f2(int i);

int f1(int j)
{
  f = &f2;
  return 1;
}
int f2(int i)
{
  assert(0);
  return 2;
}

f_ptr f = 0;

int main()
{
  int x = 0;

  x = f(x);
  assert(x == 1);
  x = f(x);
  assert(x == 2);

  return 0;
}
