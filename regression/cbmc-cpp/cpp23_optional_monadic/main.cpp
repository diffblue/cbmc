// C++23 std::optional monadic operations
#include <optional>
int main()
{
  std::optional<int> o = 42;
  auto r = o.transform([](int x) { return x * 2; });
  __CPROVER_assert(r.has_value(), "has value");
  __CPROVER_assert(*r == 84, "transformed");
}
