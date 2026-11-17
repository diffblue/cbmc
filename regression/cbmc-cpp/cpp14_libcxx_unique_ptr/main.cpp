// libc++ std::unique_ptr basic operations
#include <memory>
int main()
{
  std::unique_ptr<int> p(new int(42));
  __CPROVER_assert(*p == 42, "value");
}
