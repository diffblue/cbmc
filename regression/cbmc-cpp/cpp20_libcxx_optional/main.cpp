// libc++ std::optional in C++20 mode
#include <optional>
int main()
{
  std::optional<int> o = 42;
  __CPROVER_assert(o.has_value(), "has_value");
  __CPROVER_assert(*o == 42, "value");
}
