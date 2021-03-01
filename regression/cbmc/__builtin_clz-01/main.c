#include <assert.h>

#ifdef _MSC_VER
#  define __builtin_clz(x) __lzcnt(x)
#  define __builtin_clzll(x) __lzcnt64(x)
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
#ifdef _MSC_VER
  unsigned short f = 42;
  assert(__lzcnt16(f) == 10);
#endif
  assert(nlz2a(42) == 26);
  assert(__builtin_clz(42) == 26);
#ifndef _MSC_VER
  assert(
    __builtin_clzl(42) == 26 + (sizeof(unsigned long) - sizeof(unsigned)) * 8);
#endif
  assert(
    __builtin_clzll(42) ==
    26 + (sizeof(unsigned long long) - sizeof(unsigned)) * 8);

  unsigned int u = __VERIFIER_nondet_unsigned();
  __CPROVER_assume(u != 0);
  assert(nlz2a(u) == __builtin_clz(u));

#undef __builtin_clz
  // a failing assertion should be generated as __builtin_clz is undefined for 0
  __builtin_clz(0U);

  return 0;
}
