#include <cassert>

int main()
{
  const char buf[4] = {'a', 'b', 'c', 'b'};
  // as used by libc++'s char_traits<char>::find
  const char *p = __builtin_char_memchr(buf, 'b', 4);
  assert(p == buf + 1);
  return 0;
}
