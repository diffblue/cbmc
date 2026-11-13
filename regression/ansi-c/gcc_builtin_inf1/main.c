// The infinity built-ins have the C type their name implies, as with GCC and
// Clang. FreeBSD's <math.h> relies on this: isinf, isnan etc. are generic
// selections over float, double and long double, and INFINITY, HUGE_VALF
// and HUGE_VAL expand to these built-ins.
#define TYPE_IS(e, t) __builtin_types_compatible_p(__typeof__(e), t)

_Static_assert(TYPE_IS(__builtin_inff(), float), "inff");
_Static_assert(TYPE_IS(__builtin_huge_valf(), float), "huge_valf");
_Static_assert(TYPE_IS(__builtin_inf(), double), "inf");
_Static_assert(TYPE_IS(__builtin_huge_val(), double), "huge_val");
_Static_assert(TYPE_IS(__builtin_infl(), long double), "infl");
_Static_assert(TYPE_IS(__builtin_huge_vall(), long double), "huge_vall");

#define FP_TYPE(x) _Generic((x), float: 1, double: 2, long double: 3)

_Static_assert(FP_TYPE(__builtin_inff() / __builtin_inff()) == 1, "float");
_Static_assert(FP_TYPE(__builtin_inf() / __builtin_inf()) == 2, "double");
_Static_assert(FP_TYPE(__builtin_infl() / __builtin_infl()) == 3, "long double");

int main(void)
{
  return 0;
}
