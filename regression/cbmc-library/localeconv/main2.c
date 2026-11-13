#include <assert.h>
#include <locale.h>
#include <string.h>

int main(void)
{
  if(setlocale(LC_ALL, "") == NULL)
    return 1;

  // the locale may now differ from the "C" locale
  struct lconv *lc = localeconv();
  assert(lc->decimal_point[0] != 0);
  assert(strcmp(lc->decimal_point, ".") == 0);
  return 0;
}
