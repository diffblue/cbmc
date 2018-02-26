#include <assert.h>

#ifndef __GNUC__
int __builtin_popcount(unsigned int);
int __builtin_popcountl(unsigned long);
int __builtin_popcountll(unsigned long long);
#endif

unsigned int __VERIFIER_nondet_unsigned();
unsigned long __VERIFIER_nondet_unsigned_long();
unsigned long long __VERIFIER_nondet_unsigned_long_long();

// Hacker's Delight
// http://www.hackersdelight.org/permissions.htm
int pop4(unsigned long long x)
{
  int n = 0;

  // variant with additional bounding to make sure symbolic execution always
  // terminates without having to specify an unwinding bound
  for(int i = 0; x != 0 && i < sizeof(x) * 8; ++i)
  {
    ++n;
    x = x & (x - 1);
  }

  return n;
}

int main()
{
  assert(pop4(42) == 3);
  assert(__builtin_popcount(42) == 3);
  assert(__builtin_popcountl(42) == 3);
  assert(__builtin_popcountll(42) == 3);

  unsigned int u = __VERIFIER_nondet_unsigned();
  assert(pop4(u) == __builtin_popcount(u));

  return 0;
}
