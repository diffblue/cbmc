extern "C" void __CPROVER_assert(bool, const char *);
#include <functional>
struct One
{
  int operator()() const
  {
    return 1;
  }
};
int two()
{
  return 2;
}
int main()
{
  std::function<int()> a = One{};
  __CPROVER_assert(a() == 1, "zero-arg function from functor");
  std::function<int()> b = two;
  __CPROVER_assert(b() == 2, "zero-arg function from function pointer");
  std::function<int()> c = []() { return 3; };
  __CPROVER_assert(c() == 3, "zero-arg function from lambda");
  std::function<int(int)> d = [](int x) { return x + 4; };
  __CPROVER_assert(d(0) == 4, "one-arg function from lambda");
  return 0;
}
