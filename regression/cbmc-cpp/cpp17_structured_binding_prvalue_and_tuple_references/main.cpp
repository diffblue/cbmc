extern "C" void __CPROVER_assert(bool, const char *);
#include <map>
#include <utility>
struct S
{
  int a;
  int b;
};
S mk() { return S{5, 6}; }
template <class... Args> int sum_pair(Args &&...args)
{
  // libstdc++'s std::map::emplace(k, v) shape: a structured binding over a
  // pair of references to a parameter pack
  auto &&[a, v] = std::pair<Args &...>(args...);
  return a + v;
}
struct W
{
  int v;
  explicit W(int x) : v(x) {}
};
int main()
{
  // N5008 [dcl.struct.bind]/1: one hidden variable PER declaration -- several
  // structured bindings in one scope must not share (and retype) it.
  auto [p, q] = S{1, 2};
  auto &&[x, y] = S{7, 8};
  __CPROVER_assert(p + q == 3 && x + y == 15, "two declarations in one scope; auto&& to a prvalue aggregate");
  // [class.temporary]/6: the temporary bound to e lives as long as e
  auto &&[m, n] = mk();
  const auto &[c, d] = S{3, 4};
  __CPROVER_assert(m + n == 11 && c + d == 7, "auto&& / const auto& to prvalues");
  // tuple-like protocol ([dcl.struct.bind]/4): e is a prvalue pair; bindings
  // are references to get<i>(e)
  auto [r, s] = std::pair<int, int>(7, 8);
  auto &&[t, u] = std::pair<int, int>(3, 4);
  __CPROVER_assert(r + s == 15 && t + u == 7, "pair prvalue by value and by auto&&");
  int z = 9;
  auto &&[rz, one] = std::pair<int &, int>(z, 1);
  rz = 10;
  __CPROVER_assert(z == 10 && one == 1, "binding to a reference member writes through");
  std::pair<int &, int> pr(z, 2);
  auto &[tz, two] = pr;
  tz = 11;
  __CPROVER_assert(z == 11 && two == 2, "auto& to an lvalue pair with a reference member");
  int e1 = 2, e2 = 3;
  __CPROVER_assert(sum_pair(e1, e2) == 5 && sum_pair(1, 4) == 5, "pair<Args&...>(args...) binding");
  std::map<int, W> mp;
  auto res = mp.emplace(1, W{5});
  __CPROVER_assert(res.second && mp.at(1).v == 5, "std::map::emplace with two arguments");
  return 0;
}
