// Self-referential typedef in a class template with constexpr
// static members causes the constexpr values to be overwritten
// with unresolved expressions during recursive instantiation.
#include <cstdint>

template <intmax_t X, intmax_t Y>
struct gcd
{
  static const intmax_t value = gcd<Y, X % Y>::value;
};
template <intmax_t X>
struct gcd<X, 0>
{
  static const intmax_t value = X;
};

template <intmax_t N, intmax_t D = 1>
struct ratio
{
  static constexpr intmax_t num = N / gcd<N, D>::value;
  static constexpr intmax_t den = D / gcd<N, D>::value;
  typedef ratio<num, den> type; // self-referential typedef
};

static_assert(ratio<6, 4>::num == 3, "num");
int main()
{
}
