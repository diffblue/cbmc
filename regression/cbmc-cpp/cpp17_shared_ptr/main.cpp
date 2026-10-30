#include <memory>
int main()
{
  std::shared_ptr<int> p = std::make_shared<int>(42);
  __CPROVER_assert(*p == 42, "value");
}
