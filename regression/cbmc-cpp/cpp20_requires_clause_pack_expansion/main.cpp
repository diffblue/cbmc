// N5008 [temp.variadic]/5: `Args...` in a concept-id of a requires-clause
// expands to all deduced pack elements; `sizeof...(Args)` inside the concept
// counts them.
extern "C" void __CPROVER_assert(bool, const char *);
#include <utility>

template <typename Adaptor, typename... Args>
concept partial_app_viable =
  (Adaptor::arity > 1) && (sizeof...(Args) == Adaptor::arity - 1);

template <typename Derived>
struct range_adaptor
{
  // partial application: viable only with arity - 1 arguments
  template <typename... Args>
  requires partial_app_viable<Derived, Args...> constexpr int
  operator()(Args &&...) const
  {
    return 100;
  }
};

struct take : range_adaptor<take>
{
  template <typename R, typename D = int>
  constexpr int operator()(R &&r, D n) const
  {
    return r[0] + n;
  }
  using range_adaptor<take>::operator();
  static constexpr int arity = 2;
};

int main()
{
  int arr[] = {1, 2, 3, 4, 5};
  static_assert(partial_app_viable<take, int>, "one argument: viable");
  static_assert(!partial_app_viable<take, int, int>, "two: not viable");
  int v = take{}(arr, 3);
  __CPROVER_assert(v == 4, "two args: take's own operator()");
  int w = take{}(3);
  __CPROVER_assert(w == 100, "one arg: partial application");
  __CPROVER_assert(v == 100, "WRONG (must FAIL)");
  return 0;
}
