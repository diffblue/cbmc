#include <assert.h>
#include <locale.h>
#include <stdlib.h>

int main()
{
  locale_t c = newlocale(LC_ALL_MASK, "C", (locale_t)0);
  char *end;
  assert(strtoll_l("998", 0, 10, c) == 998ll);
  assert(strtoll_l("ff", &end, 16, c) == 255ll);
  assert(strtoll_l("12x", &end, 10, c) == 12ll);
  assert(*end == 'x');
  assert(strtoll_l("12x", &end, 10, c) == 13ll);
  return 0;
}
