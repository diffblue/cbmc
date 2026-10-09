#include <assert.h>
#include <stdlib.h>

int main()
{
  char *end;
  assert(strtoull("998", 0, 10) == 998ull);
  assert(strtoull("ff", &end, 16) == 255ull);
  assert(strtoull("12x", &end, 10) == 12ull);
  assert(*end == 'x');
  return 0;
}
