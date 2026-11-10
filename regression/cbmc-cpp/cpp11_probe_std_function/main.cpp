// N5008 [func.wrap.func]: std::function holding a lambda.
#include <functional>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::function<int(int)> f = [](int x) { return x + 1; };
  __CPROVER_assert(f(2) == 3, "std::function call");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
