#include <assert.h>

int main()
{
  char buf[4] = {'a', 'b', 'c', 'b'};

  // C23 7.26.5.2: pointer to the FIRST occurrence
  const char *p = (const char *)__builtin_memchr(buf, 'b', 4);
  assert(p != 0);
  assert(p - buf == 1);
  assert(*p == 'b');

  // absent within the searched prefix
  assert(__builtin_memchr(buf, 'c', 2) == 0);

  // n == 0 never matches
  assert(__builtin_memchr(buf, 'a', 0) == 0);

  return 0;
}
