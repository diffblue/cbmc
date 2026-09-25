#include <assert.h>
#include <stdlib.h>

int main()
{
  char *end;
  assert(strtoul("998", 0, 10) == 998ul);
  assert(strtoul("ff", &end, 16) == 255ul);
  assert(strtoul("12x", &end, 10) == 12ul);
  assert(*end == 'x');
  // C23 7.24.1.7/5: '-' negates the converted unsigned value
  assert(strtoul("-1", 0, 10) == (unsigned long)-1);
  return 0;
}
