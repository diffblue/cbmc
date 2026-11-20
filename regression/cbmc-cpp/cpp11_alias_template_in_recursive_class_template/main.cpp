// N5008 [temp.alias]/2, [temp.inst]/16: each level of a recursive class
// template naming an alias template with the same spelled arguments is a
// different specialization; none of them is a cycle.  The shape of
// libstdc++'s __parse_int::_Number_help (<bits/parse_numbers.h>), which
// converts the digits of a literal operator template's pack.
extern "C" void __CPROVER_assert(bool, const char *);

template <class T, T v>
struct integral_constant
{
  static constexpr T value = v;
};

template <unsigned long long V>
using ull_constant = integral_constant<unsigned long long, V>;

template <unsigned long long Pow, char Dig, char... Digs>
struct number_help
{
  using next = number_help<Pow / 10, Digs...>;
  using type = ull_constant<Pow *(Dig - '0') + next::type::value>;
};

template <char Dig>
struct number_help<1ULL, Dig>
{
  using type = ull_constant<Dig - '0'>;
};

template <char... Digits>
unsigned long long operator""_n()
{
  return number_help<1000, Digits...>::type::value;
}

int main()
{
  __CPROVER_assert(1234_n == 1234, "four levels");
  __CPROVER_assert(
    number_help<10000, '5', '4', '3', '2', '1'>::type::value == 54321,
    "five levels");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
