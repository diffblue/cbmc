extern "C" void __CPROVER_assert(bool, const char *);
#include <functional>
int add(int a, int b)
{
  return a + b;
}
struct S
{
  int acc = 0;
  void add3(S &s, const int &a, const int &b)
  {
    s.acc += a + b;
  }
};
struct sink
{
  sink(std::function<void(S &, const int &, const int &)> f, int k) : f(f), k(k)
  {
  }
  std::function<void(S &, const int &, const int &)> f;
  int k;
};
struct owner
{
  int acc = 0;
  owner()
    : m(std::bind(
          &owner::add,
          this,
          std::placeholders::_1,
          std::placeholders::_2,
          std::placeholders::_3),
        7)
  {
  }
  void add(S &s, const int &a, const int &b)
  {
    acc += a + b;
    s.acc += 1;
  }
  sink m;
};
int main()
{
  std::function<int(int)> f1 = std::bind(add, std::placeholders::_1, 10);
  __CPROVER_assert(
    f1(4) == 14, "bind(free function, placeholder) -> std::function");
  S s;
  std::function<void(S &, const int &, const int &)> f3 = std::bind(
    &S::add3,
    &s,
    std::placeholders::_1,
    std::placeholders::_2,
    std::placeholders::_3);
  f3(s, 2, 3);
  __CPROVER_assert(
    s.acc == 5,
    "bind(member pointer, object pointer, three placeholders) -> "
    "std::function");
  owner o;
  o.m.f(s, 2, 3);
  __CPROVER_assert(
    o.acc == 5 && s.acc == 6 && o.m.k == 7,
    "bound member function stored through a member of std::function type "
    "(goto-symex shadow_memoryt shape)");
  return 0;
}
