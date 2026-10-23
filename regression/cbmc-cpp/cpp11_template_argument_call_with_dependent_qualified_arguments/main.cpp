extern "C" void __CPROVER_assert(bool, const char *);
typedef long long intmax_t;
constexpr intmax_t gcd(intmax_t a, intmax_t b)
{
  return b == 0 ? a : gcd(b, a % b);
}
template <intmax_t N, intmax_t D = 1>
struct ratio
{
  static constexpr intmax_t num = N;
  static constexpr intmax_t den = D;
};
template <class P1, class P2>
struct common_period
{
  // N5008 [temp.arg.general]/3: the type-id interpretation of
  // `gcd(P1::num, P2::num)' requires gcd to name a type; gcd is a function,
  // so the template-argument is a call expression (the MSVC STL's
  // common_type for chrono::duration)
  using type = ratio<gcd(P1::num, P2::num), P1::den>;
};
int main()
{
  __CPROVER_assert(
    common_period<ratio<12>, ratio<18>>::type::num == 6 &&
      __is_same(common_period<ratio<1>, ratio<60>>::type, ratio<1>),
    "argument is a call");
  __CPROVER_assert(
    common_period<ratio<12>, ratio<18>>::type::num == 12, "WRONG (must FAIL)");
  return 0;
}
