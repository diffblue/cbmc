extern "C" void __CPROVER_assert(bool, const char *);
#include <functional>
int add(int a, int b)
{
  return a + b;
}
int sub3(int a, int b, int c)
{
  return a - b - c;
}
struct S
{
  int acc = 0;
  void add2(S &s, const int &a)
  {
    s.acc += a;
  }
  void add3(S &s, const int &a, const int &b)
  {
    s.acc += a + b;
  }
};
int main()
{
  auto f2 = std::bind(add, std::placeholders::_1, std::placeholders::_2);
  __CPROVER_assert(f2(1, 2) == 3, "two placeholders, prvalue arguments");
  auto f3 = std::bind(
    sub3, std::placeholders::_3, std::placeholders::_1, std::placeholders::_2);
  __CPROVER_assert(f3(1, 2, 10) == 7, "three placeholders, permuted");
  S s;
  auto m2 =
    std::bind(&S::add2, &s, std::placeholders::_1, std::placeholders::_2);
  m2(s, 3);
  __CPROVER_assert(
    s.acc == 3, "member pointer, two placeholders, lvalue argument");
  auto m3 = std::bind(
    &S::add3,
    &s,
    std::placeholders::_1,
    std::placeholders::_2,
    std::placeholders::_3);
  m3(s, 2, 3);
  __CPROVER_assert(s.acc == 8, "member pointer, three placeholders");
  return 0;
}
