#include <assert.h>
#include <string.h>

int main()
{
  char buf[4] = {'a', 'b', 'c', 'b'};

  // C23 7.26.5.2: pointer to the FIRST occurrence
  const char *p = (const char *)memchr(buf, 'b', 4);
  assert(p != 0);
  assert(p - buf == 1);
  assert(*p == 'b');

  // absent within the searched prefix
  assert(memchr(buf, 'c', 2) == 0);

  // absent entirely
  assert(memchr(buf, 'z', 4) == 0);

  // n == 0 never matches
  assert(memchr(buf, 'a', 0) == 0);

  return 0;
}
