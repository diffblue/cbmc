// C++14 std::unique_ptr basic usage
#include <memory>

int main()
{
  std::unique_ptr<int> p(new int(42));
  __CPROVER_assert(*p == 42, "unique_ptr deref");
  return 0;
}
