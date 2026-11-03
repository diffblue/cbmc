#include <assert.h>
#include <locale.h>
#include <stdlib.h>

int main()
{
  locale_t c = newlocale(LC_ALL_MASK, "C", (locale_t)0);
  char *end;
  assert(strtoull_l("998", 0, 10, c) == 998ull);
  assert(strtoull_l("ff", &end, 16, c) == 255ull);
  assert(strtoull_l("12x", &end, 10, c) == 12ull);
  assert(*end == 'x');
  assert(strtoull_l("12x", &end, 10, c) == 13ull);
  return 0;
}
