extern "C" void __CPROVER_assert(bool, const char *);
#include <functional>
#include <string>
#include <utility>
int one()
{
  return 1;
}
struct K
{
  int a;
  std::function<int()> f;
  K(int a_, const std::function<int()> &f_) : a(a_), f(f_)
  {
  }
  K(const K &) = default;
  K(K &&) = default;
};
int main()
{
  // N5008 [dcl.fct.def.default]/5, [class.copy.ctor]/14-15: an explicitly
  // defaulted copy/move constructor is the memberwise copy/move whatever the
  // members are.  Previously it was generated only for trivially copyable
  // members, otherwise left EMPTY (members default-initialised).
  std::pair<const std::string, int> p("abc", 1);
  std::pair<const std::string, int> q(p);
  __CPROVER_assert(
    q.first == "abc" && q.second == 1,
    "copy of pair<const string, int> (pair's defaulted copy constructor)");
  K k(1, one);
  K k2(k);
  __CPROVER_assert(
    k2.a == 1 && k2.f() == 1,
    "defaulted copy constructor with a std::function member");
  K k3(std::move(k2));
  __CPROVER_assert(
    k3.a == 1 && k3.f() == 1,
    "defaulted move constructor with a std::function member");
  std::pair<int, std::function<int()>> r(1, one);
  std::pair<int, std::function<int()>> s(r);
  __CPROVER_assert(s.second() == 1, "copy of pair<int, std::function>");
  return 0;
}
