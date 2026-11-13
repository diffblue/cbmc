#include <assert.h>

int main()
{
  const char buf[4] = {'a', 'b', 'c', 'b'};

  // memchr (C23 7.26.5.2) for char objects: the FIRST occurrence
  char *p = __builtin_char_memchr(buf, 'b', 4);
  assert(p != 0);
  assert(p - buf == 1);
  assert(*p == 'b');

  // absent within the searched prefix
  assert(__builtin_char_memchr(buf, 'c', 2) == 0);

  // n == 0 never matches
  assert(__builtin_char_memchr(buf, 'a', 0) == 0);

  // the value is converted to unsigned char
  const char hi[1] = {(char)0xff};
  assert(__builtin_char_memchr(hi, -1, 1) == hi);

  return 0;
}
