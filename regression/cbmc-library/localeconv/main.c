#include <assert.h>
#include <limits.h>
#include <locale.h>
#include <string.h>

int main()
{
  // C11 7.11.1.1p4: the "C" locale is in effect at program startup, with the
  // values given in C11 7.11p2
  struct lconv *c = localeconv();
  assert(c != 0);
  assert(strcmp(c->decimal_point, ".") == 0);
  assert(c->thousands_sep[0] == 0 && c->grouping[0] == 0);
  assert(c->mon_decimal_point[0] == 0 && c->mon_thousands_sep[0] == 0);
  assert(c->mon_grouping[0] == 0 && c->positive_sign[0] == 0);
  assert(c->negative_sign[0] == 0 && c->currency_symbol[0] == 0);
  assert(c->int_curr_symbol[0] == 0);
  assert(c->int_frac_digits == CHAR_MAX && c->frac_digits == CHAR_MAX);
  assert(c->p_cs_precedes == CHAR_MAX && c->p_sep_by_space == CHAR_MAX);
  assert(c->n_cs_precedes == CHAR_MAX && c->n_sep_by_space == CHAR_MAX);
  assert(c->p_sign_posn == CHAR_MAX && c->n_sign_posn == CHAR_MAX);
#ifndef _WIN32
  assert(c->int_p_cs_precedes == CHAR_MAX && c->int_n_cs_precedes == CHAR_MAX);
  assert(
    c->int_p_sep_by_space == CHAR_MAX && c->int_n_sep_by_space == CHAR_MAX);
  assert(c->int_p_sign_posn == CHAR_MAX && c->int_n_sign_posn == CHAR_MAX);
#endif
#ifdef _MSC_VER
  assert(c->_W_decimal_point[0] == L'.' && c->_W_decimal_point[1] == 0);
  assert(c->_W_thousands_sep[0] == 0 && c->_W_int_curr_symbol[0] == 0);
  assert(c->_W_currency_symbol[0] == 0 && c->_W_mon_decimal_point[0] == 0);
  assert(c->_W_mon_thousands_sep[0] == 0 && c->_W_positive_sign[0] == 0);
  assert(c->_W_negative_sign[0] == 0);
#endif
  // fails: the decimal point is "."
  __CPROVER_assert(c->decimal_point[0] == ',', "decimal point is ','");
  return 0;
}
