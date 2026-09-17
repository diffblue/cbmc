extern "C" void __CPROVER_assert(bool, const char *);
#include <functional>
#include <type_traits>
int add(int a, int b) { return a + b; }
using B = decltype(std::bind(add, std::placeholders::_1, 10));
int main()
{
  // The trait is evaluated before any call operator instance exists.
  __CPROVER_assert(std::is_same<std::__invoke_result<B &, int>::type, int>::value, "__invoke_result over _Bind, evaluated first");
  __CPROVER_assert(std::is_invocable<B &, int>::value, "is_invocable over _Bind");
  __CPROVER_assert(std::is_invocable_r<int, B &, int>::value, "is_invocable_r over _Bind");
  __CPROVER_assert(std::is_same<std::invoke_result_t<B &, int>, int>::value, "invoke_result_t over _Bind");
  auto b = std::bind(add, std::placeholders::_1, 10);
  __CPROVER_assert(b(4) == 14, "call after the traits");
  return 0;
}
