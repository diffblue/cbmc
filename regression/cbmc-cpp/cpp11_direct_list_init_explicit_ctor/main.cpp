// N5008 [dcl.init.list]/1: `T x{...}', `T{...}' and `new T{...}' are
// direct-list-initialization; [over.match.list]/1: explicit constructors are
// candidates (only copy-list-initialization must not choose one).  The
// explicit initializer-list constructor was excluded from the viability check
// for every form, so `json_objectt o{{key, value}, ...}' (an explicit
// `json_objectt(std::initializer_list<...> &&)') found "no match".
extern "C" void __CPROVER_assert(bool, const char *);
#include <initializer_list>
#include <utility>
#include <vector>

struct P1
{
  std::vector<std::pair<int, int>> v;
  explicit P1(std::initializer_list<std::pair<int, int>> il) : v(il)
  {
  }
};
struct P2
{
  int n;
  explicit P2(std::initializer_list<int> &&il) : n(il.size())
  {
  }
};
struct P3
{
  int n;
  explicit P3(std::initializer_list<int> il) : n(il.size())
  {
  }
  P3(int a, int b) : n(a * 100 + b)
  {
  }
};
int g(std::initializer_list<int> &&il)
{
  return il.size();
}
int h(const std::initializer_list<int> &il)
{
  return il.size();
}

int main()
{
  P1 a{{1, 2}, {3, 4}};
  __CPROVER_assert(
    a.v.size() == 2 && a.v[1].second == 4, "T x{...}: nested braces to pair");
  P1 b{std::make_pair(5, 6)};
  __CPROVER_assert(
    b.v.size() == 1 && b.v[0].first == 5, "T x{...}: typed element");
  P2 c{1, 2, 3};
  __CPROVER_assert(c.n == 3, "rvalue-reference initializer_list parameter");
  __CPROVER_assert(P2{1, 2}.n == 2, "T{...}");
  P2 *d = new P2{1, 2, 3, 4};
  __CPROVER_assert(d->n == 4, "new T{...}");
  delete d;
  P3 e{7, 8};
  __CPROVER_assert(
    e.n == 2, "direct-list-init: initializer-list constructor first");
  __CPROVER_assert(
    g({1, 2, 3, 4}) == 4, "parameter of type initializer_list &&");
  __CPROVER_assert(
    h({1, 2}) == 2, "parameter of type const initializer_list &");
  __CPROVER_assert(
    P2{7, 2}.n == 2, "T{...} with an initializer_list && constructor");
  std::vector<int> *v = new std::vector<int>{7, 8, 9};
  __CPROVER_assert(v->size() == 3 && (*v)[2] == 9, "new vector{...}");
  P3 *w = new P3{1, 2};
  __CPROVER_assert(
    w->n == 2, "new T{...} prefers the initializer-list constructor");
  delete v;
  delete w;
  return 0;
}
