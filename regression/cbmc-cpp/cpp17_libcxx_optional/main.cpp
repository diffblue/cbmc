// libc++ std::optional
#include <optional>
int main()
{
  std::optional<int> o = 42;
  __CPROVER_assert(o.has_value(), "has value");
}
