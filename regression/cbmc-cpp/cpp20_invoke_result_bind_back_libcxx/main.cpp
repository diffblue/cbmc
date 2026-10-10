#include <__functional/bind_back.h>

#include <functional>
#include <type_traits>

extern "C" void __CPROVER_assert(bool, const char *);

struct at
{
  int operator()(int (&a)[5], int n) const
  {
    return a[n];
  }
};

using B = decltype(std::__bind_back(at{}, 2));
using R = std::invoke_result_t<B &, int (&)[5]>;

int main()
{
  __CPROVER_assert(std::is_same_v<R, int>, "invoke_result_t");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
