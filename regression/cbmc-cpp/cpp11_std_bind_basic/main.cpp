extern "C" void __CPROVER_assert(bool, const char *);
#include <functional>
int add(int a, int b)
{
  return a + b;
}
struct S
{
  int k;
  int mul(int a) const
  {
    return k * a;
  }
};
int main()
{
  auto b1 = std::bind(add, 2, 3);
  __CPROVER_assert(b1() == 5, "bind free function, no placeholders");
  auto b2 = std::bind(add, std::placeholders::_1, 10);
  __CPROVER_assert(b2(4) == 14, "bind free function with placeholder");
  S s;
  s.k = 3;
  auto b3 = std::bind(&S::mul, &s, std::placeholders::_1);
  __CPROVER_assert(
    b3(5) == 15, "bind member function pointer + object pointer + placeholder");
  return 0;
}
