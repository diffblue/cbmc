#include <assert.h>

#ifndef __clang__
unsigned int __builtin_rotateleft32(unsigned int, unsigned int);
unsigned int __builtin_rotateright32(unsigned int, unsigned int);
#endif

unsigned nondet_unsigned(void);

int main(void)
{
  unsigned x = nondet_unsigned(), s = nondet_unsigned() % 32;
  unsigned rl = __builtin_rotateleft32(x, s);
  unsigned el = s == 0 ? x : (x << s) | (x >> (32 - s));
  assert(rl == el);

  unsigned rr = __builtin_rotateright32(x, s);
  unsigned er = s == 0 ? x : (x >> s) | (x << (32 - s));
  assert(rr == er);

  return 0;
}
