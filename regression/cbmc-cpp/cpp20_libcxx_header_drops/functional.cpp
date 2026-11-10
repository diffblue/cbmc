#include <functional>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::function<int(int)> f = [](int x) { return x + 1; };
  __CPROVER_assert(f(1) == 2, "function");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
