#include <cassert>
#include <optional>
int main()
{
  std::optional<int> opt;
  assert(!opt.has_value());
  opt = 42;
  assert(opt.has_value());
  assert(opt.value() == 42);
  return 0;
}
