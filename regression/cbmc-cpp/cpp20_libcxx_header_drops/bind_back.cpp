#include <__functional/bind_back.h>
extern "C" void __CPROVER_assert(bool, const char *);
struct at
{
  int operator()(int (&a)[5], int n) const
  {
    return a[n];
  }
};
int main()
{
  int arr[] = {1, 2, 3, 4, 5};
  auto c = std::__bind_back(at{}, 2);
  __CPROVER_assert(c(arr) == 3, "lvalue");
  __CPROVER_assert(std::__bind_back(at{}, 1)(arr) == 2, "rvalue");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
