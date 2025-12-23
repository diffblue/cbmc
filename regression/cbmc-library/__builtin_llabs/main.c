#include <assert.h>

#include <limits.h>

#ifndef __GNUC__
long long __builtin_llabs(long long);
#endif

int main()
{
  assert(__builtin_llabs(LLONG_MIN + 1) == LLONG_MAX);
  return 0;
}
