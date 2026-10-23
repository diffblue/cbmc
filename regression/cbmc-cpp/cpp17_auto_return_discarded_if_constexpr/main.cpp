// N5008 [stmt.if]/2 + [dcl.spec.auto.general]/8: a return statement in a
// discarded substatement of `if constexpr` takes no part in return type
// deduction.
extern "C" void __CPROVER_assert(bool, const char *);
#include <type_traits>

struct ref_wrap
{
  int *p;
};

template <typename R>
constexpr auto all(R &&r)
{
  if constexpr(std::is_pointer_v<std::remove_reference_t<R>>)
    return static_cast<R &&>(r); // discarded for an array argument
  else if constexpr(std::is_array_v<std::remove_reference_t<R>>)
    return ref_wrap{r};
  else
    return 0.5;
}

// [dcl.type.auto.deduct]/4: plain `auto` drops references and top-level cv
template <typename R>
constexpr auto fwd(R &&r)
{
  return static_cast<R &&>(r);
}
const int ci = 3;
auto cval()
{
  return ci;
}

template <int N>
constexpr auto pick()
{
  if constexpr(N == 0)
    return 'c';
  else if constexpr(N == 1)
    return 2u;
  else
    return 3.0;
}

int main()
{
  int arr[] = {1, 2, 3};
  auto a = all(arr);
  static_assert(__is_same(decltype(a), ref_wrap), "second branch taken");
  __CPROVER_assert(a.p[1] == 2, "wrapped array");
  int *q = arr;
  static_assert(__is_same(decltype(all(q)), int *), "first branch");
  static_assert(__is_same(decltype(all(1)), double), "else branch");
  static_assert(__is_same(decltype(pick<0>()), char), "nested chain 0");
  static_assert(__is_same(decltype(pick<1>()), unsigned), "nested chain 1");
  static_assert(__is_same(decltype(pick<2>()), double), "nested chain 2");
  __CPROVER_assert(pick<1>() == 2u, "value");
  static_assert(__is_same(decltype(fwd(q)), int *), "reference dropped");
  static_assert(__is_same(decltype(cval()), int), "top-level const dropped");
  __CPROVER_assert(*fwd(q) == 1 && cval() == 3, "forwarded values");
  __CPROVER_assert(a.p[1] == 3, "WRONG (must FAIL)");
  return 0;
}
