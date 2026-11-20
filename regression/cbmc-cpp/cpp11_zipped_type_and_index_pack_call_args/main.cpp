extern "C" void __CPROVER_assert(bool, const char *);
#include <cstddef>
#include <tuple>
int sum(int a, int b)
{
  return a * 10 + b;
}
template <std::size_t... I>
struct IS
{
};
template <class... B>
struct H
{
  std::tuple<B...> t;
  template <std::size_t... I>
  int call(IS<I...>) const
  {
    return sum(std::get<I>(t)...);
  }
  int operator()() const
  {
    return call(IS<0, 1>{});
  }
};
template <class... B>
struct H2
{
  std::tuple<B...> t;
  template <std::size_t... I>
  int call(IS<I...>) const
  {
    return sum(std::get<I>(t)...);
  }
  int operator()() const
  {
    return call(IS<0, 1>{});
  }
};
template <class F>
int mu(F &f)
{
  return f;
}
template <class... B>
struct H3
{
  std::tuple<B...> t;
  template <std::size_t... I>
  int call(IS<I...>) const
  {
    return sum(mu<const B>(std::get<I>(t))...);
  }
  int operator()() const
  {
    return call(IS<0, 1>{});
  }
};
int main()
{
  H<int, int> h{std::tuple<int, int>(2, 3)};
  __CPROVER_assert(h() == 23, "get<I>(t)... over index pack");
  H3<int, int> h3{std::tuple<int, int>(2, 3)};
  __CPROVER_assert(
    h3() == 23, "zipped type pack + index pack: mu<B>(get<I>(t))...");
  return 0;
}
