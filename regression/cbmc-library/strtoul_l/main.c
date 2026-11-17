#include <assert.h>
#include <locale.h>
#include <stdlib.h>

int main()
{
  locale_t c = newlocale(LC_ALL_MASK, "C", (locale_t)0);
  char *end;
  assert(strtoul_l("998", 0, 10, c) == 998ul);
  assert(strtoul_l("ff", &end, 16, c) == 255ul);
  assert(strtoul_l("12x", &end, 10, c) == 12ul);
  assert(*end == 'x');
  assert(strtoul_l("12x", &end, 10, c) == 13ul);
  return 0;
}
