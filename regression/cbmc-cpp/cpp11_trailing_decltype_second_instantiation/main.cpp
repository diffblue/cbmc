// A function template whose trailing return type names a parameter in a
// decltype, `auto mk(const C &c) -> rng<decltype(c.begin())>', instantiated
// for two different argument types.  The synthetic parameter symbol used to
// evaluate the decltype is shared by all specializations and kept the FIRST
// deduction's type, so the second instantiation computed rng<vector iterator>
// for a list argument and its body was dropped ("found no match for symbol
// 'rng'"; util/range.h's make_range in every TU using it twice).
extern "C" void __CPROVER_assert(bool, const char *);
#include <cstddef>

struct ints
{
  int a[3];
  const int *begin() const
  {
    return a;
  }
  const int *end() const
  {
    return a + 3;
  }
};
struct chars
{
  char s[5];
  const char *begin() const
  {
    return s;
  }
  const char *end() const
  {
    return s + 5;
  }
};
template <typename I>
struct rng
{
  I b, e;
  rng(I b, I e) : b(b), e(e)
  {
  }
  std::size_t size() const
  {
    std::size_t n = 0;
    for(I i = b; i != e; ++i)
      ++n;
    return n;
  }
};
template <typename C>
auto mk(const C &c) -> rng<decltype(c.begin())>
{
  return rng<decltype(c.begin())>(c.begin(), c.end());
}
int main()
{
  ints i{{1, 2, 3}};
  chars c{{'a', 'b', 'c', 'd', 'e'}};
  __CPROVER_assert(mk(i).size() == 3, "first instantiation");
  __CPROVER_assert(
    mk(c).size() == 5, "second instantiation, other parameter type");
  __CPROVER_assert(
    *mk(c).b == 'a' && *mk(i).b == 1, "each with its own iterator type");
  return 0;
}
