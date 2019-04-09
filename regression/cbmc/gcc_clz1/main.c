#include <assert.h>

#ifndef __GNUC__
int __builtin_clz(unsigned int);
int __builtin_clzl(unsigned long);
int __builtin_clzll(unsigned long long);
#endif

unsigned int __VERIFIER_nondet_unsigned();
unsigned long __VERIFIER_nondet_unsigned_long();
unsigned long long __VERIFIER_nondet_unsigned_long_long();

// Hacker's Delight
// http://www.hackersdelight.org/permissions.htm
int nlz2a(unsigned x)
{
  unsigned y;
  int n, c;

  n = sizeof(x) * 8;
  c = n / 2;
  // variant with additional bounding to make sure symbolic execution always
  // terminates without having to specify an unwinding bound
  int i = 0;
  do
  {
    y = x >> c;
    if(y != 0)
    {
      n = n - c;
      x = y;
    }
    c = c >> 1;
    ++i;
  } while(c != 0 && i < sizeof(x) * 8);

  return n - x;
}

int main()
{
  assert(nlz2a(42) == 26);
  assert(__builtin_clz(42) == 26);
  assert(
    __builtin_clzl(42) == 26 + (sizeof(unsigned long) - sizeof(unsigned)) * 8);
  assert(
    __builtin_clzll(42) ==
    26 + (sizeof(unsigned long long) - sizeof(unsigned)) * 8);

  unsigned int u = __VERIFIER_nondet_unsigned();
  __CPROVER_assume(u != 0);
  assert(nlz2a(u) == __builtin_clz(u));

  return 0;
}
