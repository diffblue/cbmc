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

  // n == 0 never matches, also for a null pointer (C2y, N3322)
  assert(memchr(buf, 'a', 0) == 0);
  assert(memchr(0, 'a', 0) == 0);

  // the search stops at the first match: n may exceed the object
  assert(memchr(buf, 'b', 100) == buf + 1);

  // the value is converted to unsigned char
  const char hi[1] = {(char)0xff};
  assert(memchr(hi, -1, 1) == hi);

  return 0;
}
