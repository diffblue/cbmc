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
  assert(__builtin_strstr(s, "bd") == 0);
  assert(__builtin_strpbrk(s, "cb") == s + 1);
  assert(__builtin_strpbrk(s, "xyz") == 0);
  assert(__builtin_strncmp(s, "abd", 2) == 0);
  assert(__builtin_strcmp(s, "abd") < 0);
  assert(__builtin_strlen(s) == 3);
  assert(__builtin_memcmp(s, "abd", 2) == 0);
  // variadic functions, whose models use a va_list of their own
  char buf[4];
  int x;
  __builtin_printf("%d", 1);
  __builtin_snprintf(buf, sizeof(buf), "%d", 1);
  __builtin_sscanf("1", "%d", &x);
  // a model of its own is still used
  assert(__builtin_fabs(-2.0) == 2.0);
  return 0;
}
