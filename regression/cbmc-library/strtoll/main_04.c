#include <assert.h>
#include <stdlib.h>

int main()
{
  char s[4];
  s[3] = 0;
  char *end;
  long long v = strtoll(s, &end, 0);
  // a symbolic input of bounded length
  assert(end >= s && end <= s + 3);
  assert(end != s || v == 0);
  assert(s[0] != '7' || s[1] != 0 || v == 7);
  return 0;
}
