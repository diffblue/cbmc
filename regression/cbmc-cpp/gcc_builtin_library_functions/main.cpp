// libc++'s <cmath> and <cstring> call __builtin_X, which gets the model of X.
#include <cassert>

int main()
{
  assert(__builtin_ceil(1.5) == 2.0);
  assert(__builtin_fmax(1.0, 2.0) == 2.0);
  const char *s = "abc";
  assert(__builtin_strchr(s, 'b') == s + 1);
  assert(__builtin_strlen(s) == 3);
  return 0;
}
