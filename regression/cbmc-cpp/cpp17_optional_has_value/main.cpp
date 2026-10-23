// std::optional with has_value() and operator*
#include <optional>
int main()
{
  std::optional<int> o(42);
  __CPROVER_assert(o.has_value(), "has value");
  __CPROVER_assert(*o == 42, "value");
}
