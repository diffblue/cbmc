extern "C" void __CPROVER_assert(bool, const char *);

#include <cstddef>
#include <type_traits>
#include <utility>

// a fold in the body of a lambda over the lambda's own pack is expanded
// with the lambda's call operator ([expr.prim.lambda.closure]/4), also when
// its pattern names a parameter of the enclosing function
static unsigned long digits;

struct recorder
{
  void operator()(int v) const
  {
    digits = digits * 10 + v;
  }
};

static void generic(const recorder &r)
{
  [&](auto... a) { (r(a), ...); }(1, 2, 3);
}

template <std::size_t Start, std::size_t Step, typename F>
void for_range(F &&f)
{
  [&]<std::size_t... I>(std::index_sequence<I...>) {
    (f(std::integral_constant<std::size_t, Start + I * Step>{}), ...);
  }(std::make_index_sequence<4>{});
}

int main()
{
  generic(recorder{});
  __CPROVER_assert(digits == 123, "generic lambda");

  unsigned n = 0, last = 0;
  for_range<1, 2>(
    [&](auto i)
    {
      ++n;
      last = i;
    });
  __CPROVER_assert(
    n == 4 && last == 7, "lambda with a template parameter list");

  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
