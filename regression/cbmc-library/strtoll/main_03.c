#include <assert.h>

long long __isoc23_strtoll(const char *, char **, int);

int main()
{
  char *end;
  const char *s = "0b101x";
  // C23 7.24.1.7p3: the C23 variant accepts a 0b prefix for base 0 and 2
  assert(__isoc23_strtoll(s, &end, 0) == 5);
  assert(end == s + 5);
  assert(__isoc23_strtoll(s, 0, 2) == 5);
  // but not for other bases
  assert(__isoc23_strtoll(s, 0, 16) == 0xb101);
  // an incomplete prefix is not part of the subject sequence
  s = "0b2";
  assert(__isoc23_strtoll(s, &end, 0) == 0);
  assert(end == s + 1);
  return 0;
}
