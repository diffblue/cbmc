#include <assert.h>
#include <locale.h>
#include <stdlib.h>

int main()
{
  locale_t c = newlocale(LC_ALL_MASK, "C", (locale_t)0);
  char *end;
  assert(strtol_l("998", 0, 10, c) == 998l);
  assert(strtol_l("ff", &end, 16, c) == 255l);
  assert(strtol_l("12x", &end, 10, c) == 12l);
  assert(*end == 'x');
  assert(strtol_l("12x", &end, 10, c) == 13l);
  return 0;
}
