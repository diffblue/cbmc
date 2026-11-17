#include <assert.h>
#include <limits.h>
#include <locale.h>
#include <string.h>

int main()
{
  struct lconv *c = localeconv();
  assert(strcmp(c->decimal_point, ".") == 0);
  assert(c->thousands_sep[0] == 0 && c->grouping[0] == 0);
  assert(c->currency_symbol[0] == 0 && c->negative_sign[0] == 0);
  assert(c->frac_digits == CHAR_MAX && c->n_sign_posn == CHAR_MAX);
  assert(c->decimal_point[0] == ',');
  return 0;
}
