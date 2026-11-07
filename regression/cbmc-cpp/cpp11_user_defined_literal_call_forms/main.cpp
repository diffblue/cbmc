// N5008 [lex.ext]/3-4: the form of a user-defined numeric literal's call
// depends on the literal operators found by unqualified lookup
extern "C" void __CPROVER_assert(bool, const char *);

// cooked integer and floating-point forms, beside a template of the same
// name (the cooked form wins, [lex.ext]/3)
int operator""_c(unsigned long long n)
{
  return static_cast<int>(n) + 1;
}
int operator""_c(long double f)
{
  return static_cast<int>(f * 2);
}

// raw literal operator: the source spelling as a string
int operator""_r(const char *s)
{
  int n = 0;
  while(s[n] != 0)
    ++n;
  return n;
}

// numeric literal operator template: the spelling as characters
template <char... C>
constexpr int operator""_t()
{
  return sizeof...(C);
}
// the digits' value, through a pack expansion over the characters
constexpr int value_of(const char *d, int n)
{
  return n == 0 ? 0 : value_of(d, n - 1) * 10 + (d[n - 1] - '0');
}
template <char... C>
constexpr int operator""_f()
{
  constexpr char digits[] = {C...};
  return value_of(digits, sizeof...(C));
}

// a ud-suffix starting with an integer-suffix letter: `64us' is `64' with
// ud-suffix `us' (libstdc++'s chrono literal; the suffix is reserved, so
// compilers warn)
template <char... C>
constexpr int operator""us()
{
  return sizeof...(C);
}

namespace lits
{
template <char... C>
constexpr long operator""_h()
{
  return 3600L * sizeof...(C);
}
} // namespace lits

int main()
{
  __CPROVER_assert(41_c == 42, "cooked integer");
  __CPROVER_assert(1.5_c == 3, "cooked floating");
  __CPROVER_assert(0x1F_r == 4, "raw integer");
  __CPROVER_assert(2.50_r == 4, "raw floating");
  __CPROVER_assert(1234_t == 4, "template integer");
  __CPROVER_assert(1e10_t == 4, "template floating");
  __CPROVER_assert(1'000_t == 5, "digit separator in the spelling");
  __CPROVER_assert(42345_f == 42345, "template characters");
  __CPROVER_assert(64us == 2, "suffix beginning with u");
  using namespace lits;
  __CPROVER_assert(12_h == 7200, "through a using-directive");
  __CPROVER_assert(12_h != 7200, "WRONG (must FAIL)");
}
