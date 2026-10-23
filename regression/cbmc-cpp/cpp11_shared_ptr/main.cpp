// C++11 std::shared_ptr with make_shared
#include <memory>

int main()
{
  auto p = std::make_shared<int>(42);
  __CPROVER_assert(*p == 42, "make_shared value");
  return 0;
}
