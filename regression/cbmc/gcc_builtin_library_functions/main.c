// GCC and Clang provide __builtin_X for the C library functions X, with X's
// meaning ("Other Built-in Functions Provided by GCC").  The CPROVER library
// models X; __builtin_X now gets that model (libc++'s <cmath> calls
// __builtin_ceilf, __builtin_sqrt, ...).
#include <assert.h>

int main()
{
  double d = 1.5;
  assert(__builtin_ceil(d) == 2.0);
  assert(__builtin_floorf(1.5f) == 1.0f);
  assert(__builtin_truncl(-1.5l) == -1.0l);
  assert(__builtin_sqrt(4.0) == 2.0);
  assert(__builtin_fmax(1.0, 2.0) == 2.0);
  assert(__builtin_copysign(1.0, -0.0) == -1.0);
  const char *s = "abc";
  assert(__builtin_strchr(s, 'b') == s + 1);
  assert(__builtin_strrchr(s, 'z') == 0);
  assert(__builtin_strstr(s, "bc") == s + 1);
  // a model of its own is still used
  assert(__builtin_fabs(-2.0) == 2.0);
  assert(__builtin_memchr(s, 'c', 3) == s + 2);
  return 0;
}
