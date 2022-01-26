#include <assert.h>

#ifndef __GNUC__
_Bool __builtin_add_overflow();
_Bool __builtin_add_overflow_p();
#endif

int main(void)
{
  int a, b, c, d, r;
#ifdef CONFLICT1
  assert(!__builtin_add_overflow(a, b, r));
#endif
  assert(__builtin_add_overflow(c, d));
}
